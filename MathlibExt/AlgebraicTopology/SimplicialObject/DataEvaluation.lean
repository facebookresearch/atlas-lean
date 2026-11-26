/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# Evaluation and reindexing of functor-valued simplicial data

Let A,D be arbitrary categories with independent object and morphism universes. A simplicial
datum in A→D consists of functors X_n:A→D, natural face maps d_i:X_{n+1}→X_n for i=0,…,n+1 and
degeneracies s_i:X_n→X_{n+1} for i=0,…,n, satisfying the simplicial identities. Evaluating at
a∈A gives the corresponding datum in D; varying a and varying X gives the two functorial
directions.

Currying organizes these evaluations as A→Data(D). Uncurrying forms degree functors and natural
faces and degeneracies from such an A-indexed family. Evaluation also commutes with the
associated simplicial-object construction: the comparison is identity in every simplex and
intertwines every simplex morphism.
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.SimplicialObject.Data

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a∈A, this evaluated datum has degree-n
object X_n(a), face (d_i)_a and degeneracy (s_i)_a. Applying component evaluation to the
natural-transformation identities gives all simplicial identities in D. -/
def evalObj (a : A) (X : Data (A ⥤ D)) : Data D where
  obj n := (X.obj n).obj a
  δ i := (X.δ i).app a
  σ i := (X.σ i).app a
  δ_comp_δ h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_δ h)
  δ_comp_σ_of_le h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_of_le h)
  δ_comp_σ_self := by
    intro n i
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_self (i := i))
  δ_comp_σ_succ := by
    intro n i
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_succ (i := i))
  δ_comp_σ_of_gt h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_of_gt h)
  σ_comp_σ h := by
    exact congrArg (fun f => f.app a) (X.σ_comp_σ h)

@[simp]
theorem evalObj_obj (a : A) (X : Data (A ⥤ D)) (n : ℕ) :
    (evalObj a X).obj n = (X.obj n).obj a :=
  rfl

@[simp]
theorem evalObj_δ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 2)) :
    (evalObj a X).δ i = (X.δ i).app a :=
  rfl

@[simp]
theorem evalObj_σ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 1)) :
    (evalObj a X).σ i = (X.σ i).app a :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For data X,Y in A→D, a
morphism f:X→Y and a∈A, the evaluated data morphism has degree-n component
(f_n)_a:X_n(a)→Y_n(a). It commutes with the evaluated faces and degeneracies. -/
def evalHom (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) :
    evalObj a X ⟶ evalObj a Y where
  app n := (f.app n).app a
  w_δ := by
    intro n i
    exact congrArg (fun g => g.app a) (f.w_δ i)
  w_σ := by
    intro n i
    exact congrArg (fun g => g.app a) (f.w_σ i)

@[simp]
theorem evalHom_app (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (n : ℕ) :
    (evalHom a f).app n = (f.app n).app a :=
  rfl

theorem evalHom_id (a : A) (X : Data (A ⥤ D)) :
    evalHom a (𝟙 X) = 𝟙 (evalObj a X) := by
  apply Hom.ext
  intro n
  rfl

theorem evalHom_comp {X Y Z : Data (A ⥤ D)} (a : A) (f : X ⟶ Y) (g : Y ⟶ Z) :
    evalHom a (f ≫ g) = evalHom a f ≫ evalHom a g := by
  apply Hom.ext
  intro n
  rfl

/-- Let A,D be categories with independent object and morphism universes. For a∈A, evaluation
defines a functor Data(A→D)→Data(D), sending degree functor X_n to X_n(a) and data morphism f to
components (f_n)_a. Identity and composition are preserved. -/
def evalFunctor (a : A) : Data (A ⥤ D) ⥤ Data D where
  obj X := evalObj a X
  map f := evalHom a f
  map_id X := evalHom_id a X
  map_comp f g := evalHom_comp a f g

@[simp]
theorem evalFunctor_obj_obj (a : A) (X : Data (A ⥤ D)) (n : ℕ) :
    ((evalFunctor a).obj X).obj n = (X.obj n).obj a :=
  rfl

@[simp]
theorem evalFunctor_obj_δ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 2)) :
    ((evalFunctor a).obj X).δ i = (X.δ i).app a :=
  rfl

@[simp]
theorem evalFunctor_obj_σ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 1)) :
    ((evalFunctor a).obj X).σ i = (X.σ i).app a :=
  rfl

@[simp]
theorem evalFunctor_map_app (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (n : ℕ) :
    ((evalFunctor a).map f).app n = (f.app n).app a :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a morphism f:a→b in A, the evaluated data
at a map to the data at b by degree-n component X_n(f). Naturality of each face and degeneracy
supplies the two kinds of simplicial commuting squares. -/
def evalObjMap (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) :
    evalObj a X ⟶ evalObj b X where
  app n := (X.obj n).map f
  w_δ := by
    intro n i
    exact (X.δ i).naturality f
  w_σ := by
    intro n i
    exact (X.σ i).naturality f

@[simp]
theorem evalObjMap_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (evalObjMap X f).app n = (X.obj n).map f :=
  rfl

theorem evalObjMap_id (X : Data (A ⥤ D)) (a : A) :
    evalObjMap X (𝟙 a) = 𝟙 (evalObj a X) := by
  apply Hom.ext
  intro n
  simp

theorem evalObjMap_comp (X : Data (A ⥤ D)) {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    evalObjMap X (f ≫ g) = evalObjMap X f ≫ evalObjMap X g := by
  apply Hom.ext
  intro n
  simp

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. This functor A→Data(D) sends a to the
evaluated datum X_n(a) and f:a→b to components X_n(f). It packages evaluation simultaneously in
every simplicial degree. -/
def curryObj (X : Data (A ⥤ D)) : A ⥤ Data D where
  obj a := evalObj a X
  map f := evalObjMap X f
  map_id a := by
    apply Hom.ext
    intro n
    simp
  map_comp f g := by
    apply Hom.ext
    intro n
    simp

@[simp]
theorem curryObj_obj (X : Data (A ⥤ D)) (a : A) :
    (curryObj X).obj a = evalObj a X :=
  rfl

@[simp]
theorem curryObj_map_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    ((curryObj X).map f).app n = (X.obj n).map f :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For f:X→Y in Data(A→D),
this transformation between the curried A→Data(D) functors has component at a and degree n equal
to (f_n)_a. Its naturality in a is inherited from the degree-n natural transformation f_n. -/
def curryMap {X Y : Data (A ⥤ D)} (f : X ⟶ Y) : curryObj X ⟶ curryObj Y where
  app a :=
    { app n := (f.app n).app a
      w_δ := by
        intro n i
        exact congrArg (fun g => g.app a) (f.w_δ i)
      w_σ := by
        intro n i
        exact congrArg (fun g => g.app a) (f.w_σ i) }
  naturality a b g := by
    apply Hom.ext
    intro n
    exact (f.app n).naturality g

@[simp]
theorem curryMap_app_app {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (a : A) (n : ℕ) :
    ((curryMap f).app a).app n = (f.app n).app a :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. Currying is a functor
Data(A→D)→(A→Data(D)). It sends X to the evaluated family a↦(X_n(a),d_i(a),s_i(a)) and each data
morphism to its objectwise component natural transformation. -/
def curryFunctor : Data (A ⥤ D) ⥤ (A ⥤ Data D) where
  obj X := curryObj X
  map f := curryMap f
  map_id X := by
    ext a
    apply Hom.ext
    intro n
    rfl
  map_comp := by
    intro X Y Z f g
    ext a
    apply Hom.ext
    intro n
    rfl

@[simp]
theorem curryFunctor_obj_obj (X : Data (A ⥤ D)) (a : A) :
    ((curryFunctor (A := A) (D := D)).obj X).obj a = evalObj a X :=
  rfl

@[simp]
theorem curryFunctor_obj_map_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (((curryFunctor (A := A) (D := D)).obj X).map f).app n = (X.obj n).map f :=
  rfl

@[simp]
theorem curryFunctor_map_app_app {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (a : A) (n : ℕ) :
    (((curryFunctor (A := A) (D := D)).map f).app a).app n = (f.app n).app a := by
  rfl

/-- Let A,D be categories with independent object and morphism universes. For X:A→Data(D) and n∈ℕ,
this functor A→D sends a to the degree-n object of X(a), and f:a→b to the degree-n component of
the data morphism X(f). -/
def uncurryObjObj (X : A ⥤ Data D) (n : ℕ) : A ⥤ D where
  obj a := (X.obj a).obj n
  map f := (X.map f).app n
  map_id a := by
    have h := X.map_id a
    have h_app : (X.map (𝟙 a)).app n = (𝟙 (X.obj a) : Data.Hom _ _).app n := by
      rw [h]
    calc
      (X.map (𝟙 a)).app n = (𝟙 (X.obj a) : Data.Hom _ _).app n := h_app
      _ = 𝟙 _ := rfl
  map_comp f g := by
    have h := X.map_comp f g
    calc
      (X.map (f ≫ g)).app n = (X.map f ≫ X.map g).app n := by rw [h]
      _ = (X.map f).app n ≫ (X.map g).app n := rfl

@[simp]
theorem uncurryObjObj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    (uncurryObjObj X n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryObjObj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (uncurryObjObj X n).map f = (X.map f).app n :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For X:A→Data(D), n∈ℕ and
i∈Fin(n+2), the degree-(n+1) functor maps to the degree-n functor by the natural transformation
whose a-component is the ith face of X(a). The data morphism X(f) makes these components
natural. -/
def uncurryObjδ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) :
    uncurryObjObj X (n + 1) ⟶ uncurryObjObj X n where
  app a := (X.obj a).δ i
  naturality _ _ f := (X.map f).w_δ i

@[simp]
theorem uncurryObjδ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    (uncurryObjδ X i).app a = (X.obj a).δ i :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For X:A→Data(D), n∈ℕ and
i∈Fin(n+1), the degree-n functor maps to degree n+1 with a-component the ith degeneracy of X(a).
Compatibility of X(f) with degeneracies gives naturality. -/
def uncurryObjσ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) :
    uncurryObjObj X n ⟶ uncurryObjObj X (n + 1) where
  app a := (X.obj a).σ i
  naturality _ _ f := (X.map f).w_σ i

@[simp]
theorem uncurryObjσ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    (uncurryObjσ X i).app a = (X.obj a).σ i :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For X:A→Data(D), this
datum in A→D has degree functor a↦X(a)_n and face and degeneracy transformations obtained
componentwise from X(a). The simplicial identities hold at every a and hence as natural
transformations. -/
def uncurryObj (X : A ⥤ Data D) : Data (A ⥤ D) where
  obj n := uncurryObjObj X n
  δ i := uncurryObjδ X i
  σ i := uncurryObjσ X i
  δ_comp_δ := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_δ h
  δ_comp_σ_of_le := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_σ_of_le h
  δ_comp_σ_self := by
    intro n i
    ext a
    exact (X.obj a).δ_comp_σ_self
  δ_comp_σ_succ := by
    intro n i
    ext a
    exact (X.obj a).δ_comp_σ_succ
  δ_comp_σ_of_gt := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_σ_of_gt h
  σ_comp_σ := by
    intro n i j h
    ext a
    exact (X.obj a).σ_comp_σ h

@[simp]
theorem uncurryObj_obj (X : A ⥤ Data D) (n : ℕ) :
    (uncurryObj X).obj n = uncurryObjObj X n :=
  rfl

@[simp]
theorem uncurryObj_obj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    ((uncurryObj X).obj n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryObj_obj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    ((uncurryObj X).obj n).map f = (X.map f).app n :=
  rfl

@[simp]
theorem uncurryObj_δ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) :
    (uncurryObj X).δ i = uncurryObjδ X i :=
  rfl

@[simp]
theorem uncurryObj_δ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    ((uncurryObj X).δ i).app a = (X.obj a).δ i :=
  rfl

@[simp]
theorem uncurryObj_σ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) :
    (uncurryObj X).σ i = uncurryObjσ X i :=
  rfl

@[simp]
theorem uncurryObj_σ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    ((uncurryObj X).σ i).app a = (X.obj a).σ i :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For X,Y:A→Data(D), α:X→Y
and n∈ℕ, this natural transformation between the degree-n functors has a-component (α_a)_n.
Naturality follows from the naturality of α in the data category. -/
def uncurryMapApp (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) :
    uncurryObjObj X n ⟶ uncurryObjObj Y n where
  app a := (α.app a).app n
  naturality a b f := by
    have h := α.naturality f
    calc
      (X.map f).app n ≫ (α.app b).app n
          = (X.map f ≫ α.app b).app n := rfl
      _ = (α.app a ≫ Y.map f).app n := by rw [h]
      _ = (α.app a).app n ≫ (Y.map f).app n := rfl

@[simp]
theorem uncurryMapApp_app (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) (a : A) :
    (uncurryMapApp X Y α n).app a = (α.app a).app n :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. For α:X→Y between
A→Data(D) functors, the uncurried morphism in Data(A→D) has degree-n component a↦(α_a)_n. Each
component respects faces and degeneracies because α_a is a data morphism. -/
def uncurryMap {X Y : A ⥤ Data D} (α : X ⟶ Y) :
    uncurryObj X ⟶ uncurryObj Y where
  app n := uncurryMapApp X Y α n
  w_δ := by
    intro n i
    ext a
    exact (α.app a).w_δ i
  w_σ := by
    intro n i
    ext a
    exact (α.app a).w_σ i

@[simp]
theorem uncurryMap_app (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) :
    (uncurryMap α).app n = uncurryMapApp X Y α n :=
  rfl

@[simp]
theorem uncurryMap_app_app {X Y : A ⥤ Data D} (α : X ⟶ Y) (n : ℕ) (a : A) :
    ((uncurryMap α).app n).app a = (α.app a).app n :=
  rfl

theorem uncurryMap_id (X : A ⥤ Data D) :
    uncurryMap (𝟙 X) = 𝟙 (uncurryObj X) := by
  apply Hom.ext
  intro n
  ext a
  rfl

theorem uncurryMap_comp {X Y Z : A ⥤ Data D} (α : X ⟶ Y) (β : Y ⟶ Z) :
    uncurryMap (α ≫ β) = uncurryMap α ≫ uncurryMap β := by
  apply Hom.ext
  intro n
  ext a
  rfl

/-- Let A,D be categories with independent object and morphism universes. This functor
(A→Data(D))→Data(A→D) sends each family to its degreewise functors and natural face/degeneracy
maps, and sends α to degreewise maps (α_a)_n. It preserves identities and composition. -/
def uncurryFunctor : (A ⥤ Data D) ⥤ Data (A ⥤ D) where
  obj X := uncurryObj X
  map α := uncurryMap α
  map_id X := uncurryMap_id X
  map_comp α β := uncurryMap_comp α β

@[simp]
theorem uncurryFunctor_obj_obj (X : A ⥤ Data D) (n : ℕ) :
    ((uncurryFunctor (A := A) (D := D)).obj X).obj n = uncurryObjObj X n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_obj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).obj n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_obj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (((uncurryFunctor (A := A) (D := D)).obj X).obj n).map f = (X.map f).app n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_δ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).δ i).app a = (X.obj a).δ i :=
  rfl

@[simp]
theorem uncurryFunctor_obj_σ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).σ i).app a = (X.obj a).σ i :=
  rfl

@[simp]
theorem uncurryFunctor_map_app_app {X Y : A ⥤ Data D} (α : X ⟶ Y) (n : ℕ) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).map α).app n).app a = (α.app a).app n :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a∈A and a simplex morphism f:[m]→[n],
evaluating the map of the associated simplicial object along fᵒᵖ equals the map along fᵒᵖ of the
associated evaluated datum. Both maps have source X_n(a) and target X_m(a). -/
theorem evalToSimplicial_map_eq (X : Data (A ⥤ D)) (a : A)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (X.toSimplicialObject ⋙ (evaluation A D).obj a).map f.op =
      (((evalFunctor a).obj X).toSimplicialObject).map f.op :=
  (toSimplicialObject_mapObj_map ((evaluation A D).obj a) X (f := f.op)).symm

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a∈A, evaluating the associated simplicial
object of X is naturally isomorphic to the simplicial object associated to its evaluated data at
a. Every simplex component of this comparison is identity. -/
noncomputable def evalToSimplicialIso (X : Data (A ⥤ D)) (a : A) :
    (X.toSimplicialObject ⋙ (evaluation A D).obj a) ≅
      (((evalFunctor a).obj X).toSimplicialObject) :=
  (toSimplicialFunctor_mapFunctorIso ((evaluation A D).obj a)).app X

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a∈A and Δ∈SimplexCategoryᵒᵖ, the forward
component of the comparison between associated simplicial objects after evaluation is id on the
common degree object X_{dim Δ}(a). -/
@[simp]
theorem evalToSimplicialIso_hom_app (X : Data (A ⥤ D)) (a : A)
    (Δ : SimplexCategoryᵒᵖ) :
    (evalToSimplicialIso X a).hom.app Δ = 𝟙 _ :=
  rfl

/-- Let A,D be categories with independent object and morphism universes. Let X be simplicial
face-and-degeneracy data in the functor category A→D, with degree functors X_n, natural faces
d_i:X_{n+1}→X_n and degeneracies s_i:X_n→X_{n+1}. For a∈A and Δ∈SimplexCategoryᵒᵖ, the inverse
component of the evaluation/associated-simplicial-object comparison is the identity of X_{dim
Δ}(a). -/
@[simp]
theorem evalToSimplicialIso_inv_app (X : Data (A ⥤ D)) (a : A)
    (Δ : SimplexCategoryᵒᵖ) :
    (evalToSimplicialIso X a).inv.app Δ = 𝟙 _ :=
  rfl

end CategoryTheory.SimplicialObject.Data

end
