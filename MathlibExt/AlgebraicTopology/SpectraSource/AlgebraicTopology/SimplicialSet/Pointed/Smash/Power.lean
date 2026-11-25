/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Smash/Power.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Circle
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic
import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Category.Pointed.Smash.Power
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.FiniteBijection
-- Proof-only: the degreewise description of the smash power unfolds the bodies of
-- `toSimplicialPointed` and `fromSimplicialPointed`, which are not exposed.
import all MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Basic

/-!
# Smash powers of pointed simplicial sets and the sphere sequence

The smash power `X^∧ι` of a pointed simplicial set `X`, indexed by a type `ι`, is the degreewise
smash power of pointed types: its `n`-simplices are the basepoint and the families of
`n`-simplices of `X` avoiding the basepoint in every coordinate. Bijections of the index type act
by reindexing coordinates, concatenation of families identifies `X^∧ι ∧ X^∧κ` with
`X^∧(ι ⊕ κ)`, and the smash power indexed by an empty type is the unit `S⁰`. A based map
`X ⟶ Y` acts on smash powers coordinatewise, compatibly with these operations, and the smash power
indexed by a type with a unique element is `X` itself.

Indexing by the finite-bijection groupoid gives the symmetric sequence
`PointedSSet.smashPowFunctor X : FiniteBijection ⥤ PointedSSet`, `n ↦ X^∧n`, on which
`Equiv.Perm (Fin n)` acts by permuting the smash factors. Block concatenation
`X^∧p ∧ X^∧q ≅ X^∧(p + q)` and the identification `S⁰ ≅ X^∧0` make it a braided strong monoidal
functor from the block-sum symmetric monoidal structure on `FiniteBijection` to the smash product
of pointed simplicial sets: the block swap of `FiniteBijection` corresponds to swapping the two
smash factors.

For `X` the simplicial circle `S¹ = Δ[1]/∂Δ[1]` this is the sphere sequence
`PointedSSet.smashPowFunctor PointedSSet.circle`, `n ↦ S^n = (S¹)^∧n`, with its
coordinate-permutation actions and block-concatenation multiplication `S^p ∧ S^q → S^(p+q)`.
Under Day convolution along the block sum, lax braided monoidal functors out of
`FiniteBijection` are the commutative monoids of symmetric sequences, and symmetric spectra are
the modules over the sphere sequence.

## Main definitions

* `PointedSSet.smashPow X ι`: the smash power `X^∧ι`.
* `PointedSSet.smashPowMk`: the class of a family of simplices.
* `PointedSSet.smashPowLift`: the based map out of a smash power induced by degreewise functions
  of families sending the families with a coordinate at the basepoint to the basepoint.
* `PointedSSet.smashPowReindex`, `PointedSSet.smashPowReindexIso`: the action of a bijection of
  index types.
* `PointedSSet.smashPowMap`, `PointedSSet.smashPowMapIso`: functoriality in the pointed
  simplicial set, applying a based map in every coordinate.
* `PointedSSet.smashPowAppendIso`: concatenation `X^∧ι ⊗ X^∧κ ≅ X^∧(ι ⊕ κ)`.
* `PointedSSet.smashPowUnitIso`: the identification `𝟙_ ≅ X^∧ι` for empty `ι`.
* `PointedSSet.smashPowUniqueIso`: the identification `X^∧ι ≅ X` for `ι` with a unique element.
* `PointedSSet.smashPowFunctor X`: the symmetric sequence `n ↦ X^∧n`, with its
  `Functor.Monoidal` and `Functor.Braided` instances.
* `PointedSSet.sphere k`: the simplicial `k`-sphere `S^k = (S¹)^∧k`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource.PointedSSet

variable (X : PointedSSet.{u}) {ι κ μ : Type}

/-! ### The smash power -/

/-- The smash power `X^∧ι` of a pointed simplicial set, formed degreewise: its `n`-simplices are
the basepoint and the families `ι → X_n` avoiding the basepoint in every coordinate. -/
noncomputable def smashPow (ι : Type) : PointedSSet.{u} :=
  fromSimplicialPointed.obj (toSimplicialPointed.obj X ⋙ Pointed.smashPowFunctor ι)

variable {X} {n m : SimplexCategoryᵒᵖ}

/- The basepoint of the smash power is the basepoint of the degreewise smash power of pointed
types. -/
private lemma smashPow_point :
    (X.smashPow ι).point n = (Pointed.smashPow (Pointed.of (X.point n)) ι).point :=
  point_mk _ n

/-- The class in the smash power `X^∧ι` of a family of `n`-simplices of `X`. It is the basepoint
exactly when some coordinate is the basepoint. -/
noncomputable def smashPowMk (f : ι → X.right.obj n) : (X.smashPow ι).right.obj n :=
  Pointed.smashPow.mk (X := Pointed.of (X.point n)) f

@[simp]
lemma map_smashPowMk (g : n ⟶ m) (f : ι → X.right.obj n) :
    (X.smashPow ι).right.map g (smashPowMk f) = smashPowMk (X.right.map g ∘ f) :=
  Pointed.smashPow.map_mk (X := Pointed.of (X.point n)) _ f

/-- A family represents the basepoint exactly when some coordinate is the basepoint. -/
@[simp]
lemma smashPowMk_eq_point_iff {f : ι → X.right.obj n} :
    smashPowMk f = (X.smashPow ι).point n ↔ ∃ i, f i = X.point n := by
  rw [smashPow_point]
  exact Pointed.smashPow.mk_eq_point_iff (X := Pointed.of (X.point n))

/-- Two families have the same class exactly when they are equal or both have a coordinate at
the basepoint. -/
lemma smashPowMk_eq_smashPowMk_iff {f g : ι → X.right.obj n} :
    smashPowMk f = smashPowMk g ↔
      f = g ∨ (∃ i, f i = X.point n) ∧ ∃ i, g i = X.point n :=
  Pointed.smashPow.mk_eq_mk_iff (X := Pointed.of (X.point n))

/-- Induction on the simplices of a smash power: it suffices to treat the basepoint and the
classes of families. -/
@[elab_as_elim]
lemma smashPowMk_induction {motive : (X.smashPow ι).right.obj n → Prop}
    (point : motive ((X.smashPow ι).point n)) (mk : ∀ f, motive (smashPowMk f))
    (a : (X.smashPow ι).right.obj n) : motive a :=
  Pointed.smashPow.ind (X := Pointed.of (X.point n)) (motive := motive)
    (smashPow_point (X := X) ▸ point) mk a

/-- Based maps out of a smash power are determined by their values on classes of families. -/
@[ext]
lemma smashPow_hom_ext {Y : PointedSSet.{u}} {f g : X.smashPow ι ⟶ Y}
    (h : ∀ n x, f.right.app n (smashPowMk x) = g.right.app n (smashPowMk x)) : f = g := by
  ext n a
  induction a using smashPowMk_induction with
  | point => exact (app_point f n).trans (app_point g n).symm
  | mk x => exact h n x

/-- Based maps out of a smash product of two smash powers are determined by their values on
pairs of classes of families. -/
lemma smashPow_tensor_hom_ext {Y Z : PointedSSet.{u}} {f g : X.smashPow ι ⊗ Y.smashPow κ ⟶ Z}
    (h : ∀ n x y, f.right.app n (smashMk (smashPowMk x) (smashPowMk y)) =
      g.right.app n (smashMk (smashPowMk x) (smashPowMk y))) : f = g := by
  ext n x y
  induction x using smashPowMk_induction with
  | point => simp
  | mk x =>
    induction y using smashPowMk_induction with
    | point => simp
    | mk y => exact h n x y

/-- The function on `n`-simplices out of a smash power induced by a function of families sending
the families with a coordinate at the basepoint to the basepoint. -/
private noncomputable def liftAt {Z : PointedSSet.{u}} (n : SimplexCategoryᵒᵖ)
    (F : (ι → X.right.obj n) → Z.right.obj n) (hF : ∀ f i, f i = X.point n → F f = Z.point n) :
    (X.smashPow ι).right.obj n → Z.right.obj n :=
  (Pointed.smashPow.lift (X := Pointed.of (X.point n)) (W := Pointed.of (Z.point n)) F hF).toFun

private lemma liftAt_smashPowMk {Z : PointedSSet.{u}} (F : (ι → X.right.obj n) → Z.right.obj n)
    (hF : ∀ f i, f i = X.point n → F f = Z.point n) (f : ι → X.right.obj n) :
    liftAt n F hF (smashPowMk f) = F f :=
  Pointed.smashPow.lift_mk (X := Pointed.of (X.point n)) (W := Pointed.of (Z.point n)) F hF f

private lemma liftAt_point {Z : PointedSSet.{u}} (F : (ι → X.right.obj n) → Z.right.obj n)
    (hF : ∀ f i, f i = X.point n → F f = Z.point n) :
    liftAt n F hF ((X.smashPow ι).point n) = Z.point n :=
  (congrArg _ smashPow_point).trans (Pointed.Hom.map_point _)

/-- The based map out of the smash power `X^∧ι` induced by degreewise functions of families that
send the families with a coordinate at the basepoint to the basepoint and commute with the
simplicial operators. -/
noncomputable def smashPowLift {Z : PointedSSet.{u}}
    (F : ∀ n, (ι → X.right.obj n) → Z.right.obj n)
    (hF : ∀ n f i, f i = X.point n → F n f = Z.point n)
    (nat : ∀ n m (g : n ⟶ m) f, F m (X.right.map g ∘ f) = Z.right.map g (F n f)) :
    X.smashPow ι ⟶ Z :=
  Under.homMk
    { app n := ↾(liftAt n (F n) (hF n))
      naturality n m g := by
        ext a
        simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
        induction a using smashPowMk_induction with
        | point => rw [map_point, liftAt_point, liftAt_point, map_point]
        | mk f => rw [map_smashPowMk, liftAt_smashPowMk, liftAt_smashPowMk, nat] }
    (by
      ext n a
      exact ((congrArg _ (hom_app _ n a)).trans (liftAt_point _ _)).trans (hom_app Z n a).symm)

@[simp]
lemma smashPowLift_app_smashPowMk {Z : PointedSSet.{u}}
    (F : ∀ n, (ι → X.right.obj n) → Z.right.obj n)
    (hF : ∀ n f i, f i = X.point n → F n f = Z.point n)
    (nat : ∀ n m (g : n ⟶ m) f, F m (X.right.map g ∘ f) = Z.right.map g (F n f))
    (f : ι → X.right.obj n) :
    (smashPowLift F hF nat).right.app n (smashPowMk f) = F n f :=
  liftAt_smashPowMk _ _ f

/-! ### Reindexing -/

variable (X) in
/-- The action of a bijection `e : ι ≃ κ` on smash powers, sending the class of a family `f` to
the class of `f ∘ e.symm`. -/
noncomputable def smashPowReindex (e : ι ≃ κ) : X.smashPow ι ⟶ X.smashPow κ :=
  fromSimplicialPointed.map
    { app _ := Pointed.smashPow.reindex _ e
      naturality _ _ g := Pointed.smashPow.map_reindex ((toSimplicialPointed.obj X).map g) e }

@[simp]
lemma smashPowReindex_app_smashPowMk (e : ι ≃ κ) (f : ι → X.right.obj n) :
    (X.smashPowReindex e).right.app n (smashPowMk f) = smashPowMk (f ∘ e.symm) :=
  Pointed.smashPow.reindex_mk (X := Pointed.of (X.point n)) e f

@[simp]
lemma smashPowReindex_refl : X.smashPowReindex (Equiv.refl ι) = 𝟙 _ :=
  (congrArg fromSimplicialPointed.map (NatTrans.ext (funext fun _ ↦
    Pointed.smashPow.reindex_refl))).trans (fromSimplicialPointed.map_id _)

@[simp]
lemma smashPowReindex_trans (e : ι ≃ κ) (e' : κ ≃ μ) :
    X.smashPowReindex (e.trans e') = X.smashPowReindex e ≫ X.smashPowReindex e' :=
  (congrArg fromSimplicialPointed.map (NatTrans.ext (funext fun _ ↦
    Pointed.smashPow.reindex_trans e e'))).trans (fromSimplicialPointed.map_comp _ _)

variable (X) in
/-- The isomorphism of smash powers induced by a bijection of index types. -/
noncomputable def smashPowReindexIso (e : ι ≃ κ) : X.smashPow ι ≅ X.smashPow κ where
  hom := X.smashPowReindex e
  inv := X.smashPowReindex e.symm
  hom_inv_id := by rw [← smashPowReindex_trans, Equiv.self_trans_symm, smashPowReindex_refl]
  inv_hom_id := by rw [← smashPowReindex_trans, Equiv.symm_trans_self, smashPowReindex_refl]

@[simp]
lemma smashPowReindexIso_hom (e : ι ≃ κ) :
    (X.smashPowReindexIso e).hom = X.smashPowReindex e := (rfl)

@[simp]
lemma smashPowReindexIso_inv (e : ι ≃ κ) :
    (X.smashPowReindexIso e).inv = X.smashPowReindex e.symm := (rfl)

@[reassoc (attr := simp)]
lemma smashPowReindex_comp_smashPowReindex_symm (e : ι ≃ κ) :
    X.smashPowReindex e ≫ X.smashPowReindex e.symm = 𝟙 _ :=
  (X.smashPowReindexIso e).hom_inv_id

@[reassoc (attr := simp)]
lemma smashPowReindex_symm_comp_smashPowReindex (e : ι ≃ κ) :
    X.smashPowReindex e.symm ≫ X.smashPowReindex e = 𝟙 _ :=
  (X.smashPowReindexIso e).inv_hom_id

/-! ### Concatenation -/

variable (X ι κ) in
/-- Concatenation of families, the based map `X^∧ι ⊗ X^∧κ ⟶ X^∧(ι ⊕ κ)`. -/
noncomputable def smashPowAppend : X.smashPow ι ⊗ X.smashPow κ ⟶ X.smashPow (ι ⊕ κ) :=
  smashLift
    { app n := ↾fun p ↦ Pointed.smashPow.append (X := Pointed.of (X.point n)) p.1 p.2
      naturality n m g := by
        ext p
        exact (Pointed.smashPow.map_append (X := Pointed.of (X.point n))
          (Y := Pointed.of (X.point m)) ⟨X.right.map g, X.map_point g⟩ p.1 p.2).symm }
    (fun _ _ ↦ (congrArg₂ _ smashPow_point rfl).trans
      ((Pointed.smashPow.append_point_left _).trans smashPow_point.symm))
    (fun _ _ ↦ (congrArg₂ _ rfl smashPow_point).trans
      ((Pointed.smashPow.append_point_right _).trans smashPow_point.symm))

@[simp]
lemma smashPowAppend_app_smashMk (f : ι → X.right.obj n) (g : κ → X.right.obj n) :
    (smashPowAppend X ι κ).right.app n (smashMk (smashPowMk f) (smashPowMk g)) =
      smashPowMk (Sum.elim f g) :=
  (smashLift_app_smashMk _ _ _ _ _).trans
    (Pointed.smashPow.append_mk_mk (X := Pointed.of (X.point n)) f g)

variable (X ι κ) in
/-- Splitting a family into its two blocks, the based map `X^∧(ι ⊕ κ) ⟶ X^∧ι ⊗ X^∧κ` inverse
to concatenation. -/
noncomputable def smashPowSplit : X.smashPow (ι ⊕ κ) ⟶ X.smashPow ι ⊗ X.smashPow κ :=
  smashPowLift (fun _ h ↦ smashMk (smashPowMk (h ∘ Sum.inl)) (smashPowMk (h ∘ Sum.inr)))
    (fun _ h i hi ↦ by
      rcases i with i | i
      · simp only [smashMk_eq_point_iff, smashPowMk_eq_point_iff]
        exact .inl ⟨i, hi⟩
      · simp only [smashMk_eq_point_iff, smashPowMk_eq_point_iff]
        exact .inr ⟨i, hi⟩)
    (fun _ _ _ _ ↦ by simp [Function.comp_assoc])

@[simp]
lemma smashPowSplit_app_smashPowMk (h : ι ⊕ κ → X.right.obj n) :
    (smashPowSplit X ι κ).right.app n (smashPowMk h) =
      smashMk (smashPowMk (h ∘ Sum.inl)) (smashPowMk (h ∘ Sum.inr)) :=
  smashPowLift_app_smashPowMk _ _ _ h

variable (X ι κ) in
/-- Concatenation of families identifies `X^∧ι ⊗ X^∧κ` with `X^∧(ι ⊕ κ)`. -/
noncomputable def smashPowAppendIso : X.smashPow ι ⊗ X.smashPow κ ≅ X.smashPow (ι ⊕ κ) where
  hom := smashPowAppend X ι κ
  inv := smashPowSplit X ι κ
  hom_inv_id := smashPow_tensor_hom_ext fun n f g ↦ by simp
  inv_hom_id := by
    ext n h
    simp

@[simp]
lemma smashPowAppendIso_hom : (smashPowAppendIso X ι κ).hom = smashPowAppend X ι κ := (rfl)

@[simp]
lemma smashPowAppendIso_inv : (smashPowAppendIso X ι κ).inv = smashPowSplit X ι κ := (rfl)

@[reassoc (attr := simp)]
lemma smashPowAppend_comp_smashPowSplit :
    smashPowAppend X ι κ ≫ smashPowSplit X ι κ = 𝟙 _ :=
  (smashPowAppendIso X ι κ).hom_inv_id

@[reassoc (attr := simp)]
lemma smashPowSplit_comp_smashPowAppend :
    smashPowSplit X ι κ ≫ smashPowAppend X ι κ = 𝟙 _ :=
  (smashPowAppendIso X ι κ).inv_hom_id

/-! ### The unit -/

variable (X ι) in
/-- The based map `X^∧ι ⟶ S⁰` for empty `ι`, sending the class of the empty family to the
non-basepoint simplex. -/
noncomputable def smashPowToUnit [IsEmpty ι] : X.smashPow ι ⟶ 𝟙_ PointedSSet.{u} :=
  smashPowLift (fun n _ ↦ tensorUnitSimplex n) (fun _ _ i ↦ isEmptyElim i)
    (fun _ _ _ _ ↦ (map_tensorUnitSimplex _).symm)

@[simp]
lemma smashPowToUnit_app_smashPowMk [IsEmpty ι] (f : ι → X.right.obj n) :
    (smashPowToUnit X ι).right.app n (smashPowMk f) = tensorUnitSimplex n :=
  smashPowLift_app_smashPowMk _ _ _ f

instance [IsEmpty ι] : IsIso (smashPowToUnit X ι) := by
  refine (isIso_iff_of_reflects_iso _ (Under.forget _)).1 ?_
  suffices ∀ n, IsIso (((Under.forget _).map (smashPowToUnit X ι)).app n) from
    NatIso.isIso_of_isIso_app _
  refine fun n ↦ (isIso_iff_bijective _).2 ⟨fun a b hab ↦ ?_, fun s ↦ ?_⟩
  · induction a using smashPowMk_induction with
    | point =>
      induction b using smashPowMk_induction with
      | point => rfl
      | mk g => exact (tensorUnitSimplex_ne_point n
          ((smashPowToUnit_app_smashPowMk g).symm.trans (hab.symm.trans (app_point _ n)))).elim
    | mk f =>
      induction b using smashPowMk_induction with
      | point => exact (tensorUnitSimplex_ne_point n
          ((smashPowToUnit_app_smashPowMk f).symm.trans (hab.trans (app_point _ n)))).elim
      | mk g => exact congrArg smashPowMk (Subsingleton.elim f g)
  · rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · exact ⟨_, app_point _ n⟩
    · exact ⟨smashPowMk isEmptyElim, smashPowToUnit_app_smashPowMk _⟩

variable (X ι) in
/-- The smash power indexed by an empty type is the unit `S⁰`. -/
noncomputable def smashPowUnitIso [IsEmpty ι] : 𝟙_ PointedSSet.{u} ≅ X.smashPow ι :=
  (asIso (smashPowToUnit X ι)).symm

@[simp]
lemma smashPowUnitIso_inv [IsEmpty ι] : (smashPowUnitIso X ι).inv = smashPowToUnit X ι := (rfl)

@[reassoc (attr := simp)]
lemma smashPowUnitIso_hom_comp_smashPowToUnit [IsEmpty ι] :
    (smashPowUnitIso X ι).hom ≫ smashPowToUnit X ι = 𝟙 _ :=
  (smashPowUnitIso X ι).hom_inv_id

@[reassoc (attr := simp)]
lemma smashPowToUnit_comp_smashPowUnitIso_hom [IsEmpty ι] :
    smashPowToUnit X ι ≫ (smashPowUnitIso X ι).hom = 𝟙 _ :=
  (smashPowUnitIso X ι).inv_hom_id

@[simp]
lemma smashPowUnitIso_hom_app_tensorUnitSimplex [IsEmpty ι] :
    (smashPowUnitIso X ι).hom.right.app n (tensorUnitSimplex n) = smashPowMk isEmptyElim := by
  simpa [-smashPowToUnit_comp_smashPowUnitIso_hom] using ConcreteCategory.congr_hom
    (congr_app (congrArg Under.Hom.right (smashPowUnitIso X ι).inv_hom_id) n)
    (smashPowMk (isEmptyElim : ι → X.right.obj n))

/-! ### Functoriality in the pointed simplicial set -/

section Functoriality

variable {Y Z : PointedSSet.{u}}

/-- The based map `X^∧ι ⟶ Y^∧ι` induced by a based map `f : X ⟶ Y`, applying `f` in every
coordinate. -/
noncomputable def smashPowMap (f : X ⟶ Y) (ι : Type) : X.smashPow ι ⟶ Y.smashPow ι :=
  smashPowLift (fun n x ↦ smashPowMk (f.right.app n ∘ x))
    (fun n x i hi ↦ smashPowMk_eq_point_iff.2 ⟨i, by simp [hi]⟩)
    (fun n m g x ↦ by
      rw [map_smashPowMk]
      exact congrArg smashPowMk (funext fun i ↦ NatTrans.naturality_apply f.right g (x i)))

@[simp]
lemma smashPowMap_app_smashPowMk (f : X ⟶ Y) (x : ι → X.right.obj n) :
    (smashPowMap f ι).right.app n (smashPowMk x) = smashPowMk (f.right.app n ∘ x) :=
  smashPowLift_app_smashPowMk _ _ _ x

@[simp]
lemma smashPowMap_id : smashPowMap (𝟙 X) ι = 𝟙 _ := by
  ext n x
  simp [Function.comp_def]

@[simp]
lemma smashPowMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    smashPowMap (f ≫ g) ι = smashPowMap f ι ≫ smashPowMap g ι := by
  ext n x
  simp [Function.comp_def]

/-- Applying a based map in every coordinate commutes with reindexing the coordinates. -/
@[reassoc (attr := simp)]
lemma smashPowReindex_comp_smashPowMap (f : X ⟶ Y) (e : ι ≃ κ) :
    X.smashPowReindex e ≫ smashPowMap f κ = smashPowMap f ι ≫ Y.smashPowReindex e := by
  ext n x
  simp [Function.comp_def]

/-- Applying a based map in every coordinate commutes with concatenation of families. -/
@[reassoc (attr := simp)]
lemma smashPowAppend_comp_smashPowMap (f : X ⟶ Y) :
    smashPowAppend X ι κ ≫ smashPowMap f (ι ⊕ κ) =
      (smashPowMap f ι ⊗ₘ smashPowMap f κ) ≫ smashPowAppend Y ι κ :=
  smashPow_tensor_hom_ext fun n x y ↦ by
    simp only [comp_right_app_apply, smashPowAppend_app_smashMk, smashPowMap_app_smashPowMk,
      tensorHom_app_smashMk, Sum.comp_elim]

/-- Applying a based map in every coordinate of the smash power indexed by an empty type is
compatible with the identifications with the unit `S⁰`. -/
@[reassoc (attr := simp)]
lemma smashPowMap_comp_smashPowToUnit [IsEmpty ι] (f : X ⟶ Y) :
    smashPowMap f ι ≫ smashPowToUnit Y ι = smashPowToUnit X ι := by
  ext n x
  simp

/-- The isomorphism `X^∧ι ≅ Y^∧ι` induced by an isomorphism `e : X ≅ Y`, applying `e` in every
coordinate. -/
noncomputable def smashPowMapIso (e : X ≅ Y) (ι : Type) : X.smashPow ι ≅ Y.smashPow ι where
  hom := smashPowMap e.hom ι
  inv := smashPowMap e.inv ι
  hom_inv_id := by rw [← smashPowMap_comp, e.hom_inv_id, smashPowMap_id]
  inv_hom_id := by rw [← smashPowMap_comp, e.inv_hom_id, smashPowMap_id]

@[simp]
lemma smashPowMapIso_hom (e : X ≅ Y) : (smashPowMapIso e ι).hom = smashPowMap e.hom ι := (rfl)

@[simp]
lemma smashPowMapIso_inv (e : X ≅ Y) : (smashPowMapIso e ι).inv = smashPowMap e.inv ι := (rfl)

@[reassoc (attr := simp)]
lemma smashPowMap_hom_comp_smashPowMap_inv (e : X ≅ Y) :
    smashPowMap e.hom ι ≫ smashPowMap e.inv ι = 𝟙 _ :=
  (smashPowMapIso e ι).hom_inv_id

@[reassoc (attr := simp)]
lemma smashPowMap_inv_comp_smashPowMap_hom (e : X ≅ Y) :
    smashPowMap e.inv ι ≫ smashPowMap e.hom ι = 𝟙 _ :=
  (smashPowMapIso e ι).inv_hom_id

end Functoriality

/-! ### A single smash factor -/

variable (X ι) in
/-- The smash power indexed by a type with a unique element is the pointed simplicial set itself:
the class of a family corresponds to its only coordinate. -/
noncomputable def smashPowUniqueIso [Unique ι] : X.smashPow ι ≅ X where
  hom := smashPowLift (fun _ x ↦ x default) (fun _ x i hi ↦ Unique.eq_default i ▸ hi)
    (fun _ _ _ _ ↦ rfl)
  inv := Under.homMk
    { app n := ↾fun x ↦ smashPowMk fun _ : ι ↦ x
      naturality n m g := by
        ext x
        exact (map_smashPowMk g _).symm }
    (by
      ext n a
      exact (smashPowMk_eq_point_iff.2 ⟨default, hom_app X n a⟩).trans (hom_app _ n a).symm)
  hom_inv_id := by
    ext n x
    rw [comp_right_app_apply, smashPowLift_app_smashPowMk]
    exact congrArg smashPowMk (funext fun i ↦ by rw [Unique.eq_default i])
  inv_hom_id := by
    ext n x
    simp

@[simp]
lemma smashPowUniqueIso_hom_app_smashPowMk [Unique ι] (x : ι → X.right.obj n) :
    (smashPowUniqueIso X ι).hom.right.app n (smashPowMk x) = x default :=
  smashPowLift_app_smashPowMk (fun _ (x : ι → X.right.obj _) ↦ x default) _
    (fun _ _ _ _ ↦ rfl) x

@[simp]
lemma smashPowUniqueIso_inv_app [Unique ι] (x : X.right.obj n) :
    (smashPowUniqueIso X ι).inv.right.app n x = smashPowMk fun _ ↦ x := (rfl)

/-! ### The symmetric sequence of smash powers -/

variable (X) in
/-- The symmetric sequence `n ↦ X^∧n` of smash powers of a pointed simplicial set, on which a
bijection `Fin n ≃ Fin m` acts by permuting the smash factors. -/
-- An abbreviation, so that the lemmas about `smashPow` apply to its objects and morphisms.
noncomputable abbrev smashPowFunctor : FiniteBijection ⥤ PointedSSet.{u} where
  obj n := X.smashPow (Fin n.len)
  map e := X.smashPowReindex e.toEquiv

/-- The block-concatenation isomorphism `X^∧k ⊗ X^∧l ≅ X^∧(k + l)`. -/
private noncomputable def μIso (X : PointedSSet.{u}) (k l : FiniteBijection) :
    X.smashPow (Fin k.len) ⊗ X.smashPow (Fin l.len) ≅ X.smashPow (Fin (k ⊗ l).len) :=
  smashPowAppendIso X (Fin k.len) (Fin l.len) ≪≫ X.smashPowReindexIso finSumFinEquiv

private lemma μIso_hom_app {k l : FiniteBijection} (x : Fin k.len → X.right.obj n)
    (y : Fin l.len → X.right.obj n) :
    (μIso X k l).hom.right.app n (smashMk (smashPowMk x) (smashPowMk y)) =
      smashPowMk (ι := Fin (k ⊗ l).len) (Fin.append x y) := by
  simp only [μIso, Iso.trans_hom, smashPowAppendIso_hom, smashPowReindexIso_hom, Under.comp_right,
    NatTrans.comp_app, ConcreteCategory.comp_apply, smashPowAppend_app_smashMk,
    smashPowReindex_app_smashPowMk]
  exact congrArg smashPowMk ((Equiv.eq_comp_symm finSumFinEquiv (Fin.append x y)
    (Sum.elim x y)).2 Fin.append_comp_sumElim).symm

/-- The identification `S⁰ ≅ X^∧0`. -/
private noncomputable def εIso (X : PointedSSet.{u}) :
    𝟙_ PointedSSet.{u} ≅ X.smashPow (Fin (𝟙_ FiniteBijection).len) :=
  smashPowUnitIso X (Fin 0)

private lemma εIso_hom_app :
    (εIso X).hom.right.app n (tensorUnitSimplex n) =
      smashPowMk (ι := Fin (𝟙_ FiniteBijection).len) Fin.elim0 :=
  (smashPowUnitIso_hom_app_tensorUnitSimplex (ι := Fin 0)).trans
    (congrArg smashPowMk (Subsingleton.elim _ _))

/-- Two classes agree when the families agree after reindexing the second along `e`. -/
private lemma smashPowMk_eq_smashPowMk_comp_symm {f : κ → X.right.obj n} {g : ι → X.right.obj n}
    (e : ι ≃ κ) (h : ∀ i, f (e i) = g i) : smashPowMk f = smashPowMk (g ∘ e.symm) :=
  congrArg smashPowMk ((Equiv.eq_comp_symm e f g).2 (funext h))

variable (X) in
/-- Block concatenation and `S⁰ ≅ X^∧0` make the symmetric sequence of smash powers a (strong)
monoidal functor. -/
noncomputable def smashPowFunctorCoreMonoidal : (smashPowFunctor X).CoreMonoidal where
  εIso := εIso X
  μIso := μIso X
  μIso_hom_natural_left f l := smashPow_tensor_hom_ext fun n x y ↦ by
    simp only [comp_right_app_apply, whiskerRight_app_smashMk, smashPowReindex_app_smashPowMk,
      μIso_hom_app]
    refine smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_
    induction i using Fin.addCases <;> simp
  μIso_hom_natural_right k f := smashPow_tensor_hom_ext fun n x y ↦ by
    simp only [comp_right_app_apply, whiskerLeft_app_smashMk, smashPowReindex_app_smashPowMk,
      μIso_hom_app]
    refine smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_
    induction i using Fin.addCases <;> simp
  associativity k l p := by
    ext n a z
    induction a using smashMk_induction with | h x y
    induction x using smashPowMk_induction with
    | point => simp
    | mk x =>
      induction y using smashPowMk_induction with
      | point => simp
      | mk y =>
        induction z using smashPowMk_induction with
        | point => simp
        | mk z =>
          simp only [comp_right_app_apply, whiskerLeft_app_smashMk, whiskerRight_app_smashMk,
            associator_hom_app_smashMk, smashPowReindex_app_smashPowMk, μIso_hom_app]
          refine (smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_).symm
          induction i using Fin.addCases with
          | left i => induction i using Fin.addCases <;> simp
          | right i => simp
  left_unitality k := by
    ext n s x
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    induction x using smashPowMk_induction with
    | point => simp
    | mk x =>
      simp only [comp_right_app_apply, leftUnitor_hom_app_smashMk, whiskerRight_app_smashMk,
        smashPowReindex_app_smashPowMk, εIso_hom_app, μIso_hom_app]
      refine smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_
      induction i using Fin.addCases with
      | left i => exact i.elim0
      | right i => simp only [FiniteBijection.toEquiv_leftUnitor_hom_natAdd, Fin.append_right]
  right_unitality k := by
    ext n x s
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    induction x using smashPowMk_induction with
    | point => simp
    | mk x =>
      simp only [comp_right_app_apply, rightUnitor_hom_app_smashMk, whiskerLeft_app_smashMk,
        smashPowReindex_app_smashPowMk, εIso_hom_app, μIso_hom_app]
      refine smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_
      induction i using Fin.addCases with
      | left i => simp only [FiniteBijection.toEquiv_rightUnitor_hom_castAdd, Fin.append_left]
      | right i => exact i.elim0

noncomputable instance : (smashPowFunctor X).Monoidal :=
  (smashPowFunctorCoreMonoidal X).toMonoidal

@[simp]
lemma smashPowFunctor_μ (k l : FiniteBijection) :
    Functor.LaxMonoidal.μ (smashPowFunctor X) k l =
      smashPowAppend X (Fin k.len) (Fin l.len) ≫ X.smashPowReindex finSumFinEquiv := (rfl)

@[simp]
lemma smashPowFunctor_δ (k l : FiniteBijection) :
    Functor.OplaxMonoidal.δ (smashPowFunctor X) k l =
      X.smashPowReindex finSumFinEquiv.symm ≫ smashPowSplit X (Fin k.len) (Fin l.len) := (rfl)

@[simp]
lemma smashPowFunctor_ε :
    Functor.LaxMonoidal.ε (smashPowFunctor X) = (smashPowUnitIso X (Fin 0)).hom := (rfl)

@[simp]
lemma smashPowFunctor_η :
    Functor.OplaxMonoidal.η (smashPowFunctor X) = smashPowToUnit X (Fin 0) := (rfl)

/- The next two lemmas are rewrite lemmas, not `simp` lemmas: `simp` cannot match a left-hand side
whose types mention the objects of the abbreviation `smashPowFunctor`, so it reaches `μ` and `δ`
through `smashPowFunctor_μ` and `smashPowFunctor_δ` instead. -/

/-- The multiplication of the symmetric sequence of smash powers concatenates families. -/
lemma smashPowFunctor_μ_app_smashMk {k l : FiniteBijection} (x : Fin k.len → X.right.obj n)
    (y : Fin l.len → X.right.obj n) :
    (Functor.LaxMonoidal.μ (smashPowFunctor X) k l).right.app n
        (smashMk (smashPowMk x) (smashPowMk y)) =
      smashPowMk (ι := Fin (k ⊗ l).len) (Fin.append x y) :=
  μIso_hom_app x y

/-- The comultiplication of the symmetric sequence of smash powers splits a family into its two
blocks. -/
lemma smashPowFunctor_δ_app_smashPowMk {k l : FiniteBijection}
    (h : Fin (k ⊗ l).len → X.right.obj n) :
    (Functor.OplaxMonoidal.δ (smashPowFunctor X) k l).right.app n (smashPowMk h) =
      smashMk (smashPowMk (h ∘ Fin.castAdd l.len)) (smashPowMk (h ∘ Fin.natAdd k.len)) := by
  simp [Function.comp_def]

/-- The block swap of `FiniteBijection` acts on `X^∧(k + l)` as the swap of the two smash factors
`X^∧k ∧ X^∧l`, so the symmetric sequence of smash powers is a braided monoidal functor. -/
noncomputable instance : (smashPowFunctor X).Braided where
  braided k l := smashPow_tensor_hom_ext fun n x y ↦ by
    simp only [comp_right_app_apply, braiding_hom_app_smashMk]
    rw [smashPowFunctor_μ_app_smashMk, smashPowFunctor_μ_app_smashMk,
      smashPowReindex_app_smashPowMk]
    refine (smashPowMk_eq_smashPowMk_comp_symm _ fun i ↦ ?_).symm
    induction i using Fin.addCases <;> simp

/-- A based map `f : X ⟶ Y` induces the morphism `X^∧n ⟶ Y^∧n` of symmetric sequences of smash
powers applying `f` in every coordinate. It is a monoidal natural transformation. -/
noncomputable def smashPowFunctorMap {Y : PointedSSet.{u}} (f : X ⟶ Y) :
    smashPowFunctor X ⟶ smashPowFunctor Y where
  app k := smashPowMap f (Fin k.len)

@[simp]
lemma smashPowFunctorMap_app {Y : PointedSSet.{u}} (f : X ⟶ Y) (k : FiniteBijection) :
    (smashPowFunctorMap f).app k = smashPowMap f (Fin k.len) := (rfl)

/-- Applying a based map in every coordinate is compatible with block concatenation and with the
identifications `S⁰ ≅ X^∧0`. -/
instance {Y : PointedSSet.{u}} (f : X ⟶ Y) : NatTrans.IsMonoidal (smashPowFunctorMap f) where
  unit := by
    rw [smashPowFunctor_ε, smashPowFunctor_ε, smashPowFunctorMap_app]
    exact (Iso.eq_inv_comp _).1 ((Iso.comp_inv_eq _).1
      (smashPowMap_comp_smashPowToUnit (ι := Fin 0) f))
  tensor k l := by
    rw [smashPowFunctor_μ, smashPowFunctor_μ, smashPowFunctorMap_app, smashPowFunctorMap_app,
      smashPowFunctorMap_app, Category.assoc]
    exact (congrArg (_ ≫ ·) (smashPowReindex_comp_smashPowMap f finSumFinEquiv)).trans
      (smashPowAppend_comp_smashPowMap_assoc f _)

/-- The simplicial `k`-sphere `S^k = (S¹)^∧k`, the `k`-fold smash power of the simplicial
circle. -/
noncomputable abbrev sphere (k : ℕ) : PointedSSet.{0} :=
  circle.smashPow (Fin k)

end MathlibExt.SpectraSource.PointedSSet
