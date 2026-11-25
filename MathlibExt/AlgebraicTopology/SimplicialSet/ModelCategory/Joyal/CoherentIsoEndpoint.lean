/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# The endpoint inclusion `Δ[0] ⟶ SSet.coherentIso` is categorical (the supporting result)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {C : SSet.{u}}

/-!
## Pattern maps out of prisms over `coherentIso`

Since `WalkingIso` is codiscrete, every object assignment
`Bool → Fin (n + 1) → Bool` determines a functor
`WalkingIso × Fin (n + 1) ⥤ WalkingIso`, hence pattern maps on prisms
over `coherentIso`. Their faces and composites are computed
patternwise.
-/

/-- The functor `WalkingIso × Fin (n + 1) ⥤ WalkingIso` determined by
a `Bool` pattern. -/
def cohPatternFunctor {n : ℕ} (P : Bool → Fin (n + 1) → Bool) :
    CategoryTheory.WalkingIso.{u} × Fin (n + 1) ⥤
      CategoryTheory.WalkingIso.{u} :=
  CategoryTheory.Codiscrete.functor
    (fun p : CategoryTheory.WalkingIso.{u} × Fin (n + 1) =>
      ULift.up (P (CategoryTheory.WalkingIso.equivBool p.1) p.2))

@[simp]
lemma equivBool_cohPatternFunctor_obj {n : ℕ}
    (P : Bool → Fin (n + 1) → Bool)
    (p : CategoryTheory.WalkingIso.{u} × Fin (n + 1)) :
    CategoryTheory.WalkingIso.equivBool
        ((cohPatternFunctor.{u} P).obj p) =
      P (CategoryTheory.WalkingIso.equivBool p.1) p.2 :=
  Equiv.apply_symm_apply _ _

/-- The simplex of `coherentIso` obtained from a pair `(s, t)` by a
`Bool` pattern. -/
def cohPatternSimplex {n : ℕ} (P : Bool → Fin (n + 1) → Bool)
    {Δ : SimplexCategoryᵒᵖ} (s : coherentIso.{u}.obj Δ)
    (t : (Δ[n] : SSet.{u}).obj Δ) : coherentIso.{u}.obj Δ :=
  ((cohPatternFunctor.{u} P).mapComposableArrows _).obj
    (s.prod' (stdSimplex.asOrderHom t).toFunctor)

@[simp]
lemma vertexBool_cohPatternSimplex {n : ℕ}
    (P : Bool → Fin (n + 1) → Bool) {Δ : SimplexCategoryᵒᵖ}
    (s : coherentIso.{u}.obj Δ) (t : (Δ[n] : SSet.{u}).obj Δ)
    (k : Fin (Δ.unop.len + 1)) :
    coherentIso.vertexBool (cohPatternSimplex P s t) k =
      P (coherentIso.vertexBool s k) ((stdSimplex.asOrderHom t) k) :=
  equivBool_cohPatternFunctor_obj P _

/-- The pattern map `coherentIso ⊗ Δ[n] ⟶ coherentIso` determined by
`P`. -/
def cohPatternMap {n : ℕ} (P : Bool → Fin (n + 1) → Bool) :
    coherentIso.{u} ⊗ Δ[n] ⟶ coherentIso.{u} where
  app _ := ↾fun X => cohPatternSimplex P X.1 X.2

@[simp]
lemma cohPatternMap_app {n : ℕ} (P : Bool → Fin (n + 1) → Bool)
    {Δ : SimplexCategoryᵒᵖ}
    (X : (coherentIso.{u} ⊗ Δ[n]).obj Δ) :
    (cohPatternMap P).app Δ X = cohPatternSimplex P X.1 X.2 :=
  rfl

/-- Faces of pattern maps: precomposing with `coherentIso ◁ δ i`
restricts the pattern along the order map of `δ i`. -/
lemma whiskerLeft_δ_cohPatternMap {n : ℕ}
    (P : Bool → Fin (n + 2) → Bool) (i : Fin (n + 2)) :
    (coherentIso.{u} ◁ stdSimplex.δ i) ≫ cohPatternMap P =
      cohPatternMap (fun b j => P b ((SimplexCategory.δ i).toOrderHom j)) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro X
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  simp only [NatTrans.comp_app, types_comp_apply,
    cohPatternMap_app, vertexBool_cohPatternSimplex]
  rfl

/-- The pattern map `coherentIso ⊗ Δ[n] ⟶ coherentIso ⊗ Δ[m]`
determined by a `Bool` pattern and an order map. -/
def prismPatternMap {n m : ℕ} (P : Bool → Fin (n + 1) → Bool)
    (Q : Fin (n + 1) →o Fin (m + 1)) :
    coherentIso.{u} ⊗ Δ[n] ⟶ coherentIso.{u} ⊗ Δ[m] where
  app _ := ↾fun X => ⟨cohPatternSimplex P X.1 X.2,
    stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (Q.comp (stdSimplex.asOrderHom X.2)))⟩

@[simp]
lemma prismPatternMap_app_fst {n m : ℕ} (P : Bool → Fin (n + 1) → Bool)
    (Q : Fin (n + 1) →o Fin (m + 1)) {Δ : SimplexCategoryᵒᵖ}
    (X : (coherentIso.{u} ⊗ Δ[n]).obj Δ) :
    ((prismPatternMap P Q).app Δ X).1 = cohPatternSimplex P X.1 X.2 :=
  rfl

@[simp]
lemma asOrderHom_prismPatternMap_app_snd {n m : ℕ}
    (P : Bool → Fin (n + 1) → Bool) (Q : Fin (n + 1) →o Fin (m + 1))
    {Δ : SimplexCategoryᵒᵖ} (X : (coherentIso.{u} ⊗ Δ[n]).obj Δ)
    (k : Fin (Δ.unop.len + 1)) :
    (stdSimplex.asOrderHom ((prismPatternMap P Q).app Δ X).2) k =
      Q ((stdSimplex.asOrderHom X.2) k) :=
  rfl

/-- Two simplices of `Δ[m]` whose order maps agree at every index are
equal. -/
private lemma stdSimplex_ext_asOrderHom {m : ℕ} {Δ : SimplexCategoryᵒᵖ}
    {x y : (Δ[m] : SSet.{u}).obj Δ}
    (h : ∀ k : Fin (Δ.unop.len + 1),
      (stdSimplex.asOrderHom x) k = (stdSimplex.asOrderHom y) k) :
    x = y := by
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  exact OrderHom.ext _ _ (funext fun k => h k)

private lemma asOrderHom_δ_app {n : ℕ} {Δ : SimplexCategoryᵒᵖ}
    (i : Fin (n + 2)) (t : (Δ[n] : SSet.{u}).obj Δ) :
    stdSimplex.asOrderHom ((stdSimplex.δ i).app Δ t) =
      (SimplexCategory.δ i).toOrderHom.comp (stdSimplex.asOrderHom t) :=
  OrderHom.ext _ _ (funext fun _ => rfl)

/-- Faces of prism pattern maps are prism pattern maps for the
restricted patterns. -/
lemma whiskerLeft_δ_prismPatternMap {n m : ℕ}
    (P : Bool → Fin (n + 2) → Bool) (Q : Fin (n + 2) →o Fin (m + 1))
    (i : Fin (n + 2)) :
    (coherentIso.{u} ◁ stdSimplex.δ i) ≫ prismPatternMap P Q =
      prismPatternMap (fun b j => P b ((SimplexCategory.δ i).toOrderHom j))
        (Q.comp (SimplexCategory.δ i).toOrderHom) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro X
  apply Prod.ext
  · apply coherentIso.eq_of_forall_vertexBool_eq
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      prismPatternMap_app_fst, vertexBool_cohPatternSimplex]
    rfl
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      asOrderHom_prismPatternMap_app_snd]
    rfl

/-- Composites of prism pattern maps are prism pattern maps. -/
lemma prismPatternMap_comp {n m l : ℕ}
    (P : Bool → Fin (n + 1) → Bool) (Q : Fin (n + 1) →o Fin (m + 1))
    (P' : Bool → Fin (m + 1) → Bool) (Q' : Fin (m + 1) →o Fin (l + 1)) :
    prismPatternMap P Q ≫ prismPatternMap P' Q' =
      prismPatternMap (fun b j => P' (P b j) (Q j)) (Q'.comp Q) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro X
  apply Prod.ext
  · apply coherentIso.eq_of_forall_vertexBool_eq
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      prismPatternMap_app_fst, vertexBool_cohPatternSimplex,
      asOrderHom_prismPatternMap_app_snd]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      asOrderHom_prismPatternMap_app_snd]
    rfl

/-- The identity pattern map is the identity prism. -/
lemma prismPatternMap_id {n : ℕ} :
    prismPatternMap (fun b _ => b) (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) =
      𝟙 (coherentIso.{u} ⊗ Δ[n]) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro X
  apply Prod.ext
  · apply coherentIso.eq_of_forall_vertexBool_eq
    intro k
    simp only [prismPatternMap_app_fst, vertexBool_cohPatternSimplex,
      NatTrans.id_app, types_id_apply]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [asOrderHom_prismPatternMap_app_snd, NatTrans.id_app,
      types_id_apply]
    rfl

/-- A prism pattern map whose order map is constant at `κ` is the
pattern map into `coherentIso` followed by the section at `κ`. -/
lemma prismPatternMap_const_section {n m : ℕ}
    (P : Bool → Fin (n + 1) → Bool) (κ : Fin (m + 1)) :
    prismPatternMap P
      ((SimplexCategory.const ⦋n⦌ ⦋m⦌ κ).toOrderHom) =
      cohPatternMap P ≫ prismSectionAt coherentIso κ := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro Z
  apply Prod.ext
  · simp only [NatTrans.comp_app, types_comp_apply, cohPatternMap_app,
      prismPatternMap_app_fst, prismSectionAt_app_fst]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      asOrderHom_prismPatternMap_app_snd, SimplexCategory.const_apply,
      asOrderHom_prismSectionAt_app_snd]

/-- The endofunctor of `WalkingIso` determined by a `Bool` function,
packaged through the nerve. -/
def cohBoolFunctor (f : Bool → Bool) :
    CategoryTheory.WalkingIso.{u} ⥤ CategoryTheory.WalkingIso.{u} :=
  CategoryTheory.Codiscrete.functor
    (fun w => ULift.up (f (CategoryTheory.WalkingIso.equivBool w)))

/-- The endomap of `coherentIso` determined by a `Bool` function. -/
noncomputable def cohBoolEndo (f : Bool → Bool) :
    coherentIso.{u} ⟶ coherentIso.{u} :=
  CategoryTheory.nerveMap (cohBoolFunctor.{u} f)

@[simp]
lemma vertexBool_cohBoolEndo_app (f : Bool → Bool)
    {Δ : SimplexCategoryᵒᵖ} (s : coherentIso.{u}.obj Δ)
    (k : Fin (Δ.unop.len + 1)) :
    coherentIso.vertexBool ((cohBoolEndo f).app Δ s) k =
      f (coherentIso.vertexBool s k) :=
  Equiv.apply_symm_apply _ _

@[simp]
lemma vertexBool_const_x₀_app {W : SSet.{u}} {Δ : SimplexCategoryᵒᵖ}
    (s : W.obj Δ) (k : Fin (Δ.unop.len + 1)) :
    coherentIso.vertexBool
        ((SSet.const coherentIso.x₀ : W ⟶ coherentIso.{u}).app Δ s) k =
      false :=
  rfl

lemma cohBoolFunctor_id : cohBoolFunctor.{u} id =
    𝟭 CategoryTheory.WalkingIso.{u} := by
  apply CategoryTheory.Functor.hext
  · intro w
    change CategoryTheory.WalkingIso.equivBool.symm
        (CategoryTheory.WalkingIso.equivBool w) = w
    exact Equiv.symm_apply_apply _ w
  · intro _ _ _
    apply heq_of_eq
    exact Subsingleton.elim _ _

lemma cohBoolEndo_id : cohBoolEndo.{u} id = 𝟙 coherentIso.{u} := by
  rw [cohBoolEndo, cohBoolFunctor_id, CategoryTheory.nerveMap_id]

lemma cohBoolEndo_const_false :
    cohBoolEndo.{u} (fun _ => false) =
      SSet.const coherentIso.x₀ := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  simp only [vertexBool_cohBoolEndo_app, vertexBool_const_x₀_app]

/-- Precomposing a pattern map with the section at a vertex `κ`
gives the endomap of `coherentIso` for the Bool function
`b ↦ P b κ`. -/
lemma prismSectionAt_comp_cohPatternMap {n : ℕ}
    (P : Bool → Fin (n + 1) → Bool) (κ : Fin (n + 1)) :
    prismSectionAt coherentIso.{u} κ ≫ cohPatternMap P =
      cohBoolEndo (fun b => P b κ) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  simp only [NatTrans.comp_app, types_comp_apply, cohPatternMap_app,
    vertexBool_cohPatternSimplex, prismSectionAt_app_fst,
    asOrderHom_prismSectionAt_app_snd, vertexBool_cohBoolEndo_app]

/-- The pattern map with constantly `false` Bool pattern and identity
order map is whiskering the constant endomap at `x₀`. -/
lemma prismPatternMap_constFalse_id {n : ℕ} :
    prismPatternMap (fun _ _ => false)
        (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) =
      SSet.const coherentIso.x₀ ▷ Δ[n] := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro Z
  apply Prod.ext
  · apply coherentIso.eq_of_forall_vertexBool_eq
    intro k
    simp only [prismPatternMap_app_fst, vertexBool_cohPatternSimplex,
      whiskerRight_app_apply_fst, vertexBool_const_x₀_app]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [asOrderHom_prismPatternMap_app_snd]
    rfl

/-- The pattern map for the identity Bool pattern is the first
projection. -/
lemma cohPatternMap_id_bool {n : ℕ} :
    cohPatternMap (fun b _ => b) =
      (CartesianMonoidalCategory.fst coherentIso Δ[n] :
        coherentIso.{u} ⊗ Δ[n] ⟶ coherentIso.{u}) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro Z
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  simp only [cohPatternMap_app, vertexBool_cohPatternSimplex]
  rfl

/-- An edge whose underlying simplex is degenerate and whose target
vertex equals its source vertex represents the corresponding equality
morphism in the homotopy category. -/
private lemma Edge.toHoHom_eq_eqToHom_of_edge_eq_σ {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : Edge x y) (h : y = x) (he : e.edge = Y.σ 0 y) :
    (HomotopyCategory.homMk e) =
      eqToHom (congrArg (HomotopyCategory.mk (X := Y)) h.symm) := by
  subst h
  have hed : e = Edge.id y := by
    apply Edge.ext
    rw [he, Edge.id_edge]
  rw [hed, HomotopyCategory.homMk_id]
  simp

/-- Two edges with the same underlying simplex represent morphisms
in the homotopy category that are conjugate by the equality morphisms
between their endpoints. -/
private lemma Edge.eqToHom_comp_toHoHom_comp_eqToHom {Y : SSet.{u}}
    {x y x' y' : Y _⦋0⦌} {e : Edge x y} {e' : Edge x' y'}
    (hx : x' = x) (hy : y = y') (h : e.edge = e'.edge) :
    eqToHom (congrArg (HomotopyCategory.mk (X := Y)) hx) ≫ (HomotopyCategory.homMk e) ≫
        eqToHom (congrArg (HomotopyCategory.mk (X := Y)) hy) =
      (HomotopyCategory.homMk e') := by
  subst hx
  subst hy
  have hed : e = e' := Edge.ext h
  rw [hed]
  simp

namespace coherentIso

/-- Composing the terminal map with the endpoint inclusion gives the
constant endomap of `coherentIso` at the source vertex. -/
lemma toDeltaZero_comp_endpointInclusion :
    toDeltaZero.{u} ≫ endpointInclusion =
      SSet.const coherentIso.x₀ := by
  rw [endpointInclusion_eq_const, SSet.comp_const]

/-- The constant vertex of `Fun(coherentIso, C)` attached to a vertex
`a`: the image of `a` under evaluation at the endpoint followed by the
constant-map section. -/
noncomputable def endpointConstVertex (C : SSet.{u})
    (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    ((ihom coherentIso.{u}).obj C) _⦋0⦌ :=
  ((pre toDeltaZero).app C).app (op ⦋0⦌)
    (((pre endpointInclusion).app C).app (op ⦋0⦌) a)

lemma endpointConstVertex_eq (C : SSet.{u})
    (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    endpointConstVertex C a =
      ihomVertexEquiv coherentIso C
        (SSet.const coherentIso.x₀ ≫
          (ihomVertexEquiv coherentIso C).symm a) := by
  have ha : a = ihomVertexEquiv coherentIso C
      ((ihomVertexEquiv coherentIso C).symm a) :=
    (Equiv.apply_symm_apply _ _).symm
  rw [endpointConstVertex, ha, ihomVertexEquiv_pre_app,
    ihomVertexEquiv_pre_app, ← Category.assoc,
    toDeltaZero_comp_endpointInclusion, Equiv.symm_apply_apply]

/-- The endpoint evaluation of the constant vertex is the endpoint
evaluation of the original vertex. -/
lemma endpoint_app_endpointConstVertex (C : SSet.{u})
    (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    ((pre endpointInclusion).app C).app (op ⦋0⦌)
        (endpointConstVertex C a) =
      ((pre endpointInclusion).app C).app (op ⦋0⦌) a := by
  rw [endpointConstVertex]
  have hmaps : ∀ v : ((ihom (Δ[0] : SSet.{u})).obj C) _⦋0⦌,
      ((pre endpointInclusion).app C).app (op ⦋0⦌)
          (((pre toDeltaZero).app C).app (op ⦋0⦌) v) = v := by
    intro v
    have hv : v = ihomVertexEquiv (Δ[0]) C
        ((ihomVertexEquiv (Δ[0]) C).symm v) :=
      (Equiv.apply_symm_apply _ _).symm
    rw [hv, ihomVertexEquiv_pre_app, ihomVertexEquiv_pre_app,
      ← Category.assoc, endpointInclusion_comp_toDeltaZero,
      Category.id_comp]
  exact hmaps _

/-- The Bool pattern of the contraction homotopy, from the identity
to the constant map at the source. -/
def etaPattern : Bool → Fin 2 → Bool := fun b j => if j = 0 then b else false

/-- The Bool pattern of the reversed contraction homotopy. -/
def etaInvPattern : Bool → Fin 2 → Bool := fun b j => if j = 0 then false else b

lemma prismSectionAt_zero_comp_etaPattern :
    prismSectionAt coherentIso.{u} 0 ≫ cohPatternMap etaPattern =
      𝟙 coherentIso.{u} := by
  rw [prismSectionAt_comp_cohPatternMap]
  have hf : (fun b => etaPattern b 0) = id := funext fun b => rfl
  rw [hf, cohBoolEndo_id]

lemma prismSectionAt_one_comp_etaPattern :
    prismSectionAt coherentIso.{u} 1 ≫ cohPatternMap etaPattern =
      SSet.const coherentIso.x₀ := by
  rw [prismSectionAt_comp_cohPatternMap]
  have hf : (fun b => etaPattern b 1) = fun _ => false :=
    funext fun b => rfl
  rw [hf, cohBoolEndo_const_false]

lemma prismSectionAt_zero_comp_etaInvPattern :
    prismSectionAt coherentIso.{u} 0 ≫ cohPatternMap etaInvPattern =
      SSet.const coherentIso.x₀ := by
  rw [prismSectionAt_comp_cohPatternMap]
  have hf : (fun b => etaInvPattern b 0) = fun _ => false :=
    funext fun b => rfl
  rw [hf, cohBoolEndo_const_false]

lemma prismSectionAt_one_comp_etaInvPattern :
    prismSectionAt coherentIso.{u} 1 ≫ cohPatternMap etaInvPattern =
      𝟙 coherentIso.{u} := by
  rw [prismSectionAt_comp_cohPatternMap]
  have hf : (fun b => etaInvPattern b 1) = id := funext fun b => rfl
  rw [hf, cohBoolEndo_id]

/-- The source face of a pattern prism simplex, expressed through the
section at vertex `0`. -/
lemma δ_one_ihomSimplexOfPrism_cohPatternMap_comp
    (P : Bool → Fin 2 → Bool) (g : coherentIso.{u} ⟶ C) :
    ((ihom coherentIso.{u}).obj C).δ 1
        (ihomSimplexOfPrism (cohPatternMap P ≫ g)) =
      ihomVertexEquiv coherentIso C
        ((prismSectionAt coherentIso 0 ≫ cohPatternMap P) ≫ g) := by
  rw [δ_one_ihomSimplexOfPrism]
  congr 1

/-- The target face of a pattern prism simplex, expressed through the
section at vertex `1`. -/
lemma δ_zero_ihomSimplexOfPrism_cohPatternMap_comp
    (P : Bool → Fin 2 → Bool) (g : coherentIso.{u} ⟶ C) :
    ((ihom coherentIso.{u}).obj C).δ 0
        (ihomSimplexOfPrism (cohPatternMap P ≫ g)) =
      ihomVertexEquiv coherentIso C
        ((prismSectionAt coherentIso 1 ≫ cohPatternMap P) ≫ g) := by
  rw [δ_zero_ihomSimplexOfPrism]
  congr 1

variable (C : SSet.{u})

/-- The contraction edge in `Fun(coherentIso, C)` from a vertex to its
constant vertex, given by the pattern prism of its classifying map. -/
noncomputable def etaEdge (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    Edge a (endpointConstVertex C a) :=
  edgeOfPrism
    (cohPatternMap etaPattern ≫ (ihomVertexEquiv coherentIso C).symm a)
    (by
      rw [δ_one_ihomSimplexOfPrism_cohPatternMap_comp,
        prismSectionAt_zero_comp_etaPattern, Category.id_comp]
      exact (Equiv.apply_symm_apply _ _))
    (by
      rw [endpointConstVertex_eq,
        δ_zero_ihomSimplexOfPrism_cohPatternMap_comp,
        prismSectionAt_one_comp_etaPattern])

/-- The reversed contraction edge in `Fun(coherentIso, C)` from the
constant vertex back to the original vertex. -/
noncomputable def etaInvEdge (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    Edge (endpointConstVertex C a) a :=
  edgeOfPrism
    (cohPatternMap etaInvPattern ≫ (ihomVertexEquiv coherentIso C).symm a)
    (by
      rw [endpointConstVertex_eq,
        δ_one_ihomSimplexOfPrism_cohPatternMap_comp,
        prismSectionAt_zero_comp_etaInvPattern])
    (by
      rw [δ_zero_ihomSimplexOfPrism_cohPatternMap_comp,
        prismSectionAt_one_comp_etaInvPattern, Category.id_comp]
      exact (Equiv.apply_symm_apply _ _))

@[simp]
lemma etaEdge_edge (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    (etaEdge C a).edge =
      ihomSimplexOfPrism
        (cohPatternMap etaPattern ≫ (ihomVertexEquiv coherentIso C).symm a) :=
  rfl

@[simp]
lemma etaInvEdge_edge (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    (etaInvEdge C a).edge =
      ihomSimplexOfPrism
        (cohPatternMap etaInvPattern ≫
          (ihomVertexEquiv coherentIso C).symm a) :=
  rfl

/-- The `Δ[2]` Bool pattern `[b, false, b]`, exhibiting the composite
of the contraction edge with its reverse as the identity. -/
def pointPattern : Bool → Fin 3 → Bool := fun b j => if j = 1 then false else b

/-- Faces of `Δ[2]` pattern prism simplices whose restricted pattern
is a prescribed `Δ[1]` pattern. -/
lemma δ_cohPatternMap_comp_eq {P : Bool → Fin 3 → Bool}
    {Q : Bool → Fin 2 → Bool} (i : Fin 3)
    (h : ∀ b j, P b ((SimplexCategory.δ i).toOrderHom j) = Q b j)
    (g : coherentIso.{u} ⟶ C) :
    ((ihom coherentIso.{u}).obj C).δ i
        (ihomSimplexOfPrism (cohPatternMap P ≫ g)) =
      ihomSimplexOfPrism (cohPatternMap Q ≫ g) := by
  rw [δ_ihomSimplexOfPrism, ← Category.assoc, whiskerLeft_δ_cohPatternMap]
  have hPQ : (fun b j => P b ((SimplexCategory.δ i).toOrderHom j)) = Q :=
    funext fun b => funext fun j => h b j
  rw [hPQ]

/-- The `2`-simplex exhibiting `etaEdge` followed by `etaInvEdge` as
the identity edge. -/
noncomputable def etaCompStruct (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    Edge.CompStruct (etaEdge C a) (etaInvEdge C a) (Edge.id a) :=
  Edge.CompStruct.mk
    (ihomSimplexOfPrism
      (cohPatternMap pointPattern ≫ (ihomVertexEquiv coherentIso C).symm a))
    (by
      rw [etaEdge_edge]
      exact δ_cohPatternMap_comp_eq C 2
        (fun b j => by fin_cases j <;> rfl) _)
    (by
      rw [etaInvEdge_edge]
      exact δ_cohPatternMap_comp_eq C 0
        (fun b j => by fin_cases j <;> rfl) _)
    (by
      rw [Edge.id_edge]
      calc ((ihom coherentIso.{u}).obj C).δ 1
              (ihomSimplexOfPrism (cohPatternMap pointPattern ≫
                (ihomVertexEquiv coherentIso C).symm a))
          = ihomSimplexOfPrism (cohPatternMap (fun b _ => b) ≫
              (ihomVertexEquiv coherentIso C).symm a) :=
            δ_cohPatternMap_comp_eq C 1
              (fun b j => by fin_cases j <;> rfl) _
        _ = ((ihom coherentIso.{u}).obj C).σ 0 a := by
              rw [cohPatternMap_id_bool, ihomSimplexOfPrism_fst,
                Equiv.apply_symm_apply])

/-- In the homotopy category, the contraction edge followed by its
reverse is the identity, at the original vertex. -/
lemma eta_toHoHom_comp_etaInv (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    (HomotopyCategory.homMk (etaEdge C a)) ≫ (HomotopyCategory.homMk (etaInvEdge C a)) =
      𝟙 (HomotopyCategory.mk a :
        hoFunctor.obj ((ihom coherentIso.{u}).obj C)) := by
  rw [← HomotopyCategory.homMk_id]
  exact HomotopyCategory.homMk_comp_homMk (etaCompStruct C a)

/-- Precomposing the contraction patterns with the endpoint in the
`coherentIso` variable yields the degenerate prism at the endpoint,
since both patterns send `false` to `false` at every index. -/
lemma whiskerRight_endpoint_cohPatternMap_eta :
    (endpointInclusion.{u} ▷ Δ[1]) ≫ cohPatternMap etaPattern =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫
        endpointInclusion := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro Z
  obtain ⟨Z₁, Z₂⟩ := Z
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  have hsrc : coherentIso.vertexBool
      (endpointInclusion.{u}.app Δ Z₁) k = false := by
    rw [endpointInclusion_eq_const]
    exact vertexBool_const_x₀_app Z₁ k
  have hpat : ∀ j : Fin 2, etaPattern false j = false := fun j => by
    by_cases hj : j = 0 <;> simp [etaPattern, hj]
  have hL : ((endpointInclusion.{u} ▷ Δ[1] ≫ cohPatternMap etaPattern).app Δ)
        (Z₁, Z₂) =
      cohPatternSimplex etaPattern (endpointInclusion.{u}.app Δ Z₁) Z₂ :=
    rfl
  have hR : ((CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫
        endpointInclusion).app Δ) (Z₁, Z₂) =
      endpointInclusion.app Δ Z₁ :=
    rfl
  rw [hL, hR, vertexBool_cohPatternSimplex, hsrc]
  exact hpat _

lemma whiskerRight_endpoint_cohPatternMap_etaInv :
    (endpointInclusion.{u} ▷ Δ[1]) ≫ cohPatternMap etaInvPattern =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫
        endpointInclusion := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro Z
  obtain ⟨Z₁, Z₂⟩ := Z
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro k
  have hsrc : coherentIso.vertexBool
      (endpointInclusion.{u}.app Δ Z₁) k = false := by
    rw [endpointInclusion_eq_const]
    exact vertexBool_const_x₀_app Z₁ k
  have hpat : ∀ j : Fin 2, etaInvPattern false j = false := fun j => by
    by_cases hj : j = 0 <;> simp [etaInvPattern, hj]
  have hL : ((endpointInclusion.{u} ▷ Δ[1] ≫ cohPatternMap etaInvPattern).app Δ)
        (Z₁, Z₂) =
      cohPatternSimplex etaInvPattern (endpointInclusion.{u}.app Δ Z₁) Z₂ :=
    rfl
  have hR : ((CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫
        endpointInclusion).app Δ) (Z₁, Z₂) =
      endpointInclusion.app Δ Z₁ :=
    rfl
  rw [hL, hR, vertexBool_cohPatternSimplex, hsrc]
  exact hpat _

/-- The evaluation of the contraction edge at the endpoint is the
identity edge in the homotopy category (as an equality morphism). -/
lemma etaEdge_map_endpoint_toHoHom
    (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    (HomotopyCategory.homMk ((etaEdge C a).map ((pre endpointInclusion).app C))) =
      eqToHom (congrArg HomotopyCategory.mk
        (endpoint_app_endpointConstVertex C a).symm) := by
  apply Edge.toHoHom_eq_eqToHom_of_edge_eq_σ _
    (endpoint_app_endpointConstVertex C a)
  rw [Edge.map_edge, etaEdge_edge, ihomSimplexOfPrism_pre_app,
    ← Category.assoc, whiskerRight_endpoint_cohPatternMap_eta,
    Category.assoc, ihomSimplexOfPrism_fst, ← ihomVertexEquiv_pre_app,
    Equiv.apply_symm_apply, endpoint_app_endpointConstVertex]

/-- The evaluation of the reversed contraction edge at the endpoint
is the identity edge in the homotopy category (as an equality
morphism). -/
lemma etaInvEdge_map_endpoint_toHoHom
    (a : ((ihom coherentIso.{u}).obj C) _⦋0⦌) :
    (HomotopyCategory.homMk ((etaInvEdge C a).map ((pre endpointInclusion).app C))) =
      eqToHom (congrArg HomotopyCategory.mk
        (endpoint_app_endpointConstVertex C a)) := by
  apply Edge.toHoHom_eq_eqToHom_of_edge_eq_σ _
    (endpoint_app_endpointConstVertex C a).symm
  rw [Edge.map_edge, etaInvEdge_edge, ihomSimplexOfPrism_pre_app,
    ← Category.assoc, whiskerRight_endpoint_cohPatternMap_etaInv,
    Category.assoc, ihomSimplexOfPrism_fst, ← ihomVertexEquiv_pre_app,
    Equiv.apply_symm_apply]

/-!
## Naturality of the contraction edge

The diagonal of the naturality square of `etaEdge` at an edge `ε` is
the edge of the prism obtained from `ε` by the prism pattern map with
Bool pattern `etaPattern` and identity order map. The two triangles
are the `Δ[2]` pattern maps with order maps `(0,0,1)` and `(0,1,1)`,
the degeneracy order maps of the simplex category.
-/

/-- Composing the section at `κ` with a prism pattern map. -/
lemma prismSectionAt_comp_prismPatternMap {n m : ℕ}
    (P : Bool → Fin (n + 1) → Bool) (Q : Fin (n + 1) →o Fin (m + 1))
    (κ : Fin (n + 1)) :
    prismSectionAt coherentIso.{u} κ ≫ prismPatternMap P Q =
      cohBoolEndo (fun b => P b κ) ≫ prismSectionAt coherentIso (Q κ) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  have hAppL : ((prismSectionAt coherentIso.{u} κ ≫
        prismPatternMap P Q).app Δ) s =
      (prismPatternMap P Q).app Δ ((prismSectionAt coherentIso κ).app Δ s) :=
    rfl
  have hAppR : ((cohBoolEndo (fun b => P b κ) ≫
        prismSectionAt coherentIso (Q κ)).app Δ) s =
      (prismSectionAt coherentIso (Q κ)).app Δ
        ((cohBoolEndo (fun b => P b κ)).app Δ s) :=
    rfl
  rw [hAppL, hAppR]
  apply Prod.ext
  · simp only [prismPatternMap_app_fst, prismSectionAt_app_fst]
    apply coherentIso.eq_of_forall_vertexBool_eq
    intro k
    simp only [vertexBool_cohPatternSimplex,
      asOrderHom_prismSectionAt_app_snd, vertexBool_cohBoolEndo_app]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [asOrderHom_prismPatternMap_app_snd,
      asOrderHom_prismSectionAt_app_snd]

/-- The source endpoint restriction of the prism of an edge. -/
lemma prismSectionAt_zero_comp_ihomPrism_edge
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌} (ε : Edge a b) :
    prismSectionAt coherentIso.{u} 0 ≫ ihomPrismOfSimplex ε.edge =
      (ihomVertexEquiv coherentIso C).symm a := by
  apply (ihomVertexEquiv coherentIso C).injective
  have h := δ_one_ihomSimplexOfPrism_comp (X := coherentIso.{u}) (C := C)
    (𝟙 (coherentIso.{u} ⊗ Δ[1])) (ihomPrismOfSimplex ε.edge)
  simp only [Category.comp_id, Category.id_comp,
    ihomSimplexOfPrism_ihomPrismOfSimplex] at h
  rw [← h, Edge.src_eq, Equiv.apply_symm_apply]

/-- The target endpoint restriction of the prism of an edge. -/
lemma prismSectionAt_one_comp_ihomPrism_edge
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌} (ε : Edge a b) :
    prismSectionAt coherentIso.{u} 1 ≫ ihomPrismOfSimplex ε.edge =
      (ihomVertexEquiv coherentIso C).symm b := by
  apply (ihomVertexEquiv coherentIso C).injective
  have h := δ_zero_ihomSimplexOfPrism_comp (X := coherentIso.{u}) (C := C)
    (𝟙 (coherentIso.{u} ⊗ Δ[1])) (ihomPrismOfSimplex ε.edge)
  simp only [Category.comp_id, Category.id_comp,
    ihomSimplexOfPrism_ihomPrismOfSimplex] at h
  rw [← h, Edge.tgt_eq, Equiv.apply_symm_apply]

lemma cohBoolEndo_etaPattern_zero :
    cohBoolEndo.{u} (fun b => etaPattern b 0) = 𝟙 coherentIso.{u} := by
  have hf : (fun b => etaPattern b 0) = id := funext fun b => rfl
  rw [hf, cohBoolEndo_id]

lemma cohBoolEndo_etaPattern_one :
    cohBoolEndo.{u} (fun b => etaPattern b 1) =
      SSet.const coherentIso.x₀ := by
  have hf : (fun b => etaPattern b 1) = fun _ => false :=
    funext fun b => rfl
  rw [hf, cohBoolEndo_const_false]

/-- The diagonal edge of the naturality square of `etaEdge` at `ε`. -/
noncomputable def diagEdge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) : Edge a (endpointConstVertex C b) :=
  edgeOfPrism
    (prismPatternMap etaPattern OrderHom.id ≫ ihomPrismOfSimplex ε.edge)
    (by
      rw [δ_one_ihomSimplexOfPrism_comp,
        prismSectionAt_comp_prismPatternMap, Category.assoc]
      have hid0 : (OrderHom.id : Fin 2 →o Fin 2) 0 = 0 := rfl
      rw [hid0, prismSectionAt_zero_comp_ihomPrism_edge C ε,
        cohBoolEndo_etaPattern_zero, Category.id_comp]
      exact (Equiv.apply_symm_apply _ _))
    (by
      rw [endpointConstVertex_eq, δ_zero_ihomSimplexOfPrism_comp,
        prismSectionAt_comp_prismPatternMap, Category.assoc]
      have hid1 : (OrderHom.id : Fin 2 →o Fin 2) 1 = 1 := rfl
      rw [hid1, prismSectionAt_one_comp_ihomPrism_edge C ε,
        cohBoolEndo_etaPattern_one])

@[simp]
lemma diagEdge_edge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) :
    (diagEdge C ε).edge =
      ihomSimplexOfPrism
        (prismPatternMap etaPattern OrderHom.id ≫
          ihomPrismOfSimplex ε.edge) :=
  rfl

/-- The prism describing the image of an edge under endpoint
evaluation followed by the constant section. -/
lemma map_endpoint_map_toDeltaZero_edge
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌} (ε : Edge a b) :
    ((ε.map ((pre endpointInclusion).app C)).map
        ((pre toDeltaZero).app C)).edge =
      ihomSimplexOfPrism
        ((SSet.const coherentIso.x₀ ▷ Δ[1]) ≫ ihomPrismOfSimplex ε.edge) := by
  set P := ihomPrismOfSimplex ε.edge with hP
  have hε : ihomSimplexOfPrism P = ε.edge :=
    ihomSimplexOfPrism_ihomPrismOfSimplex _
  rw [Edge.map_edge, Edge.map_edge, ← hε, ihomSimplexOfPrism_pre_app,
    ihomSimplexOfPrism_pre_app, ← Category.assoc, ← comp_whiskerRight,
    toDeltaZero_comp_endpointInclusion]

/-- The Bool pattern of the first naturality triangle. -/
def sqOnePattern : Bool → Fin 3 → Bool := fun b j => if j = 0 then b else false

/-- The Bool pattern of the second naturality triangle. -/
def sqTwoPattern : Bool → Fin 3 → Bool := fun b j => if j = 2 then false else b

/-- The prism pattern map of the first naturality triangle, with
order map `(0, 0, 1)`. -/
def sqOneMap : coherentIso.{u} ⊗ Δ[2] ⟶ coherentIso.{u} ⊗ Δ[1] :=
  prismPatternMap sqOnePattern
    (SimplexCategory.σ (0 : Fin 2)).toOrderHom

/-- The prism pattern map of the second naturality triangle, with
order map `(0, 1, 1)`. -/
def sqTwoMap : coherentIso.{u} ⊗ Δ[2] ⟶ coherentIso.{u} ⊗ Δ[1] :=
  prismPatternMap sqTwoPattern
    (SimplexCategory.σ (1 : Fin 2)).toOrderHom

lemma whiskerLeft_δ_two_sqOneMap :
    (coherentIso.{u} ◁ stdSimplex.δ 2) ≫ sqOneMap =
      prismPatternMap etaPattern
        ((SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).toOrderHom) := by
  rw [sqOneMap, whiskerLeft_δ_prismPatternMap]
  congr 1
  · funext b j
    fin_cases j <;> rfl
  · exact OrderHom.ext _ _ (funext fun j => by fin_cases j <;> rfl)

lemma whiskerLeft_δ_zero_sqOneMap :
    (coherentIso.{u} ◁ stdSimplex.δ 0) ≫ sqOneMap =
      prismPatternMap (fun _ _ => false) OrderHom.id := by
  rw [sqOneMap, whiskerLeft_δ_prismPatternMap]
  congr 1

lemma whiskerLeft_δ_one_sqOneMap :
    (coherentIso.{u} ◁ stdSimplex.δ 1) ≫ sqOneMap =
      prismPatternMap etaPattern OrderHom.id := by
  rw [sqOneMap, whiskerLeft_δ_prismPatternMap]
  congr 1
  · funext b j
    fin_cases j <;> rfl
  · exact OrderHom.ext _ _ (funext fun j => by fin_cases j <;> rfl)

lemma whiskerLeft_δ_two_sqTwoMap :
    (coherentIso.{u} ◁ stdSimplex.δ 2) ≫ sqTwoMap =
      prismPatternMap (fun b _ => b) OrderHom.id := by
  rw [sqTwoMap, whiskerLeft_δ_prismPatternMap]
  congr 1
  · funext b j
    fin_cases j <;> rfl
  · exact OrderHom.ext _ _ (funext fun j => by fin_cases j <;> rfl)

lemma whiskerLeft_δ_zero_sqTwoMap :
    (coherentIso.{u} ◁ stdSimplex.δ 0) ≫ sqTwoMap =
      prismPatternMap etaPattern
        ((SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).toOrderHom) := by
  rw [sqTwoMap, whiskerLeft_δ_prismPatternMap]
  congr 1
  · funext b j
    fin_cases j <;> rfl
  · exact OrderHom.ext _ _ (funext fun j => by fin_cases j <;> rfl)

lemma whiskerLeft_δ_one_sqTwoMap :
    (coherentIso.{u} ◁ stdSimplex.δ 1) ≫ sqTwoMap =
      prismPatternMap etaPattern OrderHom.id := by
  rw [sqTwoMap, whiskerLeft_δ_prismPatternMap]
  congr 1
  · funext b j
    fin_cases j <;> rfl
  · exact OrderHom.ext _ _ (funext fun j => by fin_cases j <;> rfl)

/-- The image of an edge under endpoint evaluation followed by the
constant section, transported to the constant vertices. -/
noncomputable def gfEdge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) :
    Edge (endpointConstVertex C a) (endpointConstVertex C b) :=
  ((ε.map ((pre endpointInclusion).app C)).map
    ((pre toDeltaZero).app C)).ofEq rfl rfl

@[simp]
lemma gfEdge_edge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) :
    (gfEdge C ε).edge =
      ((ε.map ((pre endpointInclusion).app C)).map
        ((pre toDeltaZero).app C)).edge :=
  rfl

lemma gfEdge_toHoHom {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) :
    (HomotopyCategory.homMk (gfEdge C ε)) =
      (HomotopyCategory.homMk ((ε.map ((pre endpointInclusion).app C)).map
        ((pre toDeltaZero).app C))) :=
  rfl

/-- The first naturality triangle: `etaEdge` at the source, followed
by the constant-section image of the evaluation of `ε`, is the
diagonal edge. -/
noncomputable def etaCompSqOne
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌} (ε : Edge a b) :
    Edge.CompStruct (etaEdge C a) (gfEdge C ε) (diagEdge C ε) :=
  Edge.CompStruct.mk
    (ihomSimplexOfPrism (sqOneMap ≫ ihomPrismOfSimplex ε.edge))
    (by
      rw [etaEdge_edge, δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_two_sqOneMap, prismPatternMap_const_section,
        Category.assoc, prismSectionAt_zero_comp_ihomPrism_edge C ε])
    (by
      rw [gfEdge_edge, map_endpoint_map_toDeltaZero_edge C ε,
        δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_zero_sqOneMap, prismPatternMap_constFalse_id])
    (by
      rw [diagEdge_edge, δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_one_sqOneMap])

/-- The second naturality triangle: `ε`, followed by `etaEdge` at the
target, is the diagonal edge. -/
noncomputable def etaCompSqTwo
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌} (ε : Edge a b) :
    Edge.CompStruct ε (etaEdge C b) (diagEdge C ε) :=
  Edge.CompStruct.mk
    (ihomSimplexOfPrism (sqTwoMap ≫ ihomPrismOfSimplex ε.edge))
    (by
      rw [δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_two_sqTwoMap, prismPatternMap_id, Category.id_comp,
        ihomSimplexOfPrism_ihomPrismOfSimplex])
    (by
      rw [etaEdge_edge, δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_zero_sqTwoMap, prismPatternMap_const_section,
        Category.assoc, prismSectionAt_one_comp_ihomPrism_edge C ε])
    (by
      rw [diagEdge_edge, δ_ihomSimplexOfPrism, ← Category.assoc,
        whiskerLeft_δ_one_sqTwoMap])

/-- Precomposition with the terminal map after the endpoint
inclusion is the identity on functor objects out of `Δ[0]`. -/
lemma pre_toDeltaZero_comp_pre_endpointInclusion :
    ((pre toDeltaZero).app C) ≫ ((pre endpointInclusion).app C) =
      𝟙 ((ihom (Δ[0] : SSet.{u})).obj C) := by
  rw [← NatTrans.comp_app, ← pre_map, endpointInclusion_comp_toDeltaZero,
    pre_id]
  rfl

/-- The image of an edge of `Fun(Δ[0], C)` under the constant section,
transported to the constant vertices of its endpoints. -/
noncomputable def sectionEdge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε' : Edge (((pre endpointInclusion).app C).app (op ⦋0⦌) a)
      (((pre endpointInclusion).app C).app (op ⦋0⦌) b)) :
    Edge (endpointConstVertex C a) (endpointConstVertex C b) :=
  (ε'.map ((pre toDeltaZero).app C)).ofEq rfl rfl

@[simp]
lemma sectionEdge_edge {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε' : Edge (((pre endpointInclusion).app C).app (op ⦋0⦌) a)
      (((pre endpointInclusion).app C).app (op ⦋0⦌) b)) :
    (sectionEdge C ε').edge = (ε'.map ((pre toDeltaZero).app C)).edge :=
  rfl

/-- Evaluating the constant section of an edge back at the endpoint
recovers the edge's simplex. -/
lemma sectionEdge_map_endpoint_edge
    {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε' : Edge (((pre endpointInclusion).app C).app (op ⦋0⦌) a)
      (((pre endpointInclusion).app C).app (op ⦋0⦌) b)) :
    ((sectionEdge C ε').map ((pre endpointInclusion).app C)).edge =
      ε'.edge := by
  rw [Edge.map_edge, sectionEdge_edge, Edge.map_edge]
  have h : ((pre endpointInclusion).app C).app (op ⦋1⦌)
        (((pre toDeltaZero).app C).app (op ⦋1⦌) ε'.edge) =
      (((pre toDeltaZero).app C) ≫
        ((pre endpointInclusion).app C)).app (op ⦋1⦌) ε'.edge :=
    rfl
  rw [h, pre_toDeltaZero_comp_pre_endpointInclusion]
  rfl

/-- **Naturality of the contraction edge** in the homotopy category
of `Fun(coherentIso, C)`. -/
lemma eta_natural {a b : ((ihom coherentIso.{u}).obj C) _⦋0⦌}
    (ε : Edge a b) :
    (HomotopyCategory.homMk ε) ≫ (HomotopyCategory.homMk (etaEdge C b)) =
      (HomotopyCategory.homMk (etaEdge C a)) ≫ (HomotopyCategory.homMk (gfEdge C ε)) :=
  (HomotopyCategory.homMk_comp_homMk (etaCompSqTwo C ε)).trans
    (HomotopyCategory.homMk_comp_homMk (etaCompSqOne C ε)).symm

variable [Quasicategory C]

/-- **The edge extension property holds for every quasicategory.**
The required edge represents the composite, in the homotopy
category, of the contraction edge at the source, the constant
section of the given edge, and the reversed contraction edge at the
target; its evaluation is the given edge because both contraction
edges evaluate to equality morphisms and the middle edge evaluates
back to the given edge. -/
theorem edgeExtensionProperty_of_quasicategory :
    edgeExtensionProperty C := by
  intro a a' ε'
  obtain ⟨ε, hε⟩ := Edge.exists_homMk_eq
    ((HomotopyCategory.homMk (etaEdge C a)) ≫ (HomotopyCategory.homMk (sectionEdge C ε')) ≫
      (HomotopyCategory.homMk (etaInvEdge C a')))
  refine ⟨ε, ?_⟩
  show (HomotopyCategory.homMk (ε.map ((pre endpointInclusion).app C))) =
    (HomotopyCategory.homMk ε')
  rw [← mapHomotopyCategory_map_homMk, hε]
  simp only [Functor.map_comp, mapHomotopyCategory_map_homMk,
    etaEdge_map_endpoint_toHoHom, etaInvEdge_map_endpoint_toHoHom]
  exact Edge.eqToHom_comp_toHoHom_comp_eqToHom
    (endpoint_app_endpointConstVertex C a).symm
    (endpoint_app_endpointConstVertex C a')
    (sectionEdge_map_endpoint_edge C ε')

/-- **The composition extension property holds for every
quasicategory.** Naturality of the contraction edge transports the
composition relation of the evaluated edges to a composition
relation conjugated by the contraction edge, and cancelling the
contraction edge against its reverse gives the relation before
evaluation. -/
theorem compExtensionProperty_of_quasicategory :
    compExtensionProperty C := by
  intro a b c ε₁ ε₂ ε₁₂ hComp
  obtain ⟨hc⟩ := hComp
  have heval : (HomotopyCategory.homMk (ε₁.map ((pre endpointInclusion).app C))) ≫
        (HomotopyCategory.homMk (ε₂.map ((pre endpointInclusion).app C))) =
      (HomotopyCategory.homMk (ε₁₂.map ((pre endpointInclusion).app C))) :=
    HomotopyCategory.homMk_comp_homMk hc
  have hGF : (HomotopyCategory.homMk (gfEdge C ε₁)) ≫ (HomotopyCategory.homMk (gfEdge C ε₂)) =
      (HomotopyCategory.homMk (gfEdge C ε₁₂)) := by
    have hcongr := congrArg
      (mapHomotopyCategory ((pre toDeltaZero).app C)).map heval
    rw [Functor.map_comp] at hcongr
    rw [gfEdge_toHoHom, gfEdge_toHoHom, gfEdge_toHoHom,
      ← mapHomotopyCategory_map_homMk ((pre toDeltaZero).app C) (ε₁.map ((pre
        endpointInclusion).app C)),
      ← mapHomotopyCategory_map_homMk ((pre toDeltaZero).app C) (ε₂.map ((pre
        endpointInclusion).app C)),
      ← mapHomotopyCategory_map_homMk ((pre toDeltaZero).app C) (ε₁₂.map ((pre
        endpointInclusion).app C))]
    exact hcongr
  have hkey : ((HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂)) ≫
    (HomotopyCategory.homMk (etaEdge C c)) =
      (HomotopyCategory.homMk ε₁₂) ≫ (HomotopyCategory.homMk (etaEdge C c)) := by
    calc ((HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂)) ≫
      (HomotopyCategory.homMk (etaEdge C c))
        = (HomotopyCategory.homMk ε₁) ≫ ((HomotopyCategory.homMk ε₂) ≫
          (HomotopyCategory.homMk (etaEdge C c))) :=
          Category.assoc _ _ _
      _ = (HomotopyCategory.homMk ε₁) ≫ ((HomotopyCategory.homMk (etaEdge C b)) ≫
        (HomotopyCategory.homMk (gfEdge C ε₂))) := by
          rw [eta_natural]
      _ = ((HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk (etaEdge C b))) ≫
        (HomotopyCategory.homMk (gfEdge C ε₂)) :=
          (Category.assoc _ _ _).symm
      _ = ((HomotopyCategory.homMk (etaEdge C a)) ≫ (HomotopyCategory.homMk (gfEdge C ε₁))) ≫
            (HomotopyCategory.homMk (gfEdge C ε₂)) := by
          rw [eta_natural]
      _ = (HomotopyCategory.homMk (etaEdge C a)) ≫
            ((HomotopyCategory.homMk (gfEdge C ε₁)) ≫ (HomotopyCategory.homMk (gfEdge C ε₂))) :=
          Category.assoc _ _ _
      _ = (HomotopyCategory.homMk (etaEdge C a)) ≫ (HomotopyCategory.homMk (gfEdge C ε₁₂)) := by
          rw [hGF]
      _ = (HomotopyCategory.homMk ε₁₂) ≫ (HomotopyCategory.homMk (etaEdge C c)) :=
          (eta_natural C ε₁₂).symm
  have hcomp : (HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂) =
    (HomotopyCategory.homMk ε₁₂) := by
    calc (HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂)
        = ((HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂)) ≫
            ((HomotopyCategory.homMk (etaEdge C c)) ≫ (HomotopyCategory.homMk (etaInvEdge
              C c))) := by
          rw [eta_toHoHom_comp_etaInv, Category.comp_id]
      _ = (((HomotopyCategory.homMk ε₁) ≫ (HomotopyCategory.homMk ε₂)) ≫
        (HomotopyCategory.homMk (etaEdge C c))) ≫
            (HomotopyCategory.homMk (etaInvEdge C c)) :=
          Category.assoc _ _ _
      _ = ((HomotopyCategory.homMk ε₁₂) ≫ (HomotopyCategory.homMk (etaEdge C c))) ≫
            (HomotopyCategory.homMk (etaInvEdge C c)) := by
          rw [hkey]
      _ = (HomotopyCategory.homMk ε₁₂) ≫
            ((HomotopyCategory.homMk (etaEdge C c)) ≫ (HomotopyCategory.homMk (etaInvEdge C c))) :=
          Category.assoc _ _ _
      _ = (HomotopyCategory.homMk ε₁₂) := by
          rw [eta_toHoHom_comp_etaInv, Category.comp_id]
  exact Edge.nonempty_compStruct_of_homMk_comp_eq hcomp

end coherentIso

/-- **Main theorem (the supporting result).** The endpoint inclusion
`Δ[0] ⟶ SSet.coherentIso` is a Joyal categorical equivalence,
unconditionally. This discharges the two prism-extension hypotheses
of the conditional the supporting result theorem
`SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions`. -/
theorem categoricalEquivalences.coherentIso_endpointInclusion :
    categoricalEquivalences.{u} coherentIso.endpointInclusion :=
  categoricalEquivalences.coherentIso_endpointInclusion_of_extensions
    fun C hC => by
      have := hC
      exact ⟨coherentIso.edgeExtensionProperty_of_quasicategory C,
        coherentIso.compExtensionProperty_of_quasicategory C⟩

/-- Endpoint evaluation into a quasicategory is an equivalence of
ordinary categories, unconditionally. -/
theorem coherentIso.hoPre_endpointInclusion_isEquivalence
    (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map
      ((pre coherentIso.endpointInclusion).app C)).toFunctor.IsEquivalence :=
  coherentIso.hoPre_endpointInclusion_isEquivalence_of_extensions C
    (coherentIso.edgeExtensionProperty_of_quasicategory C)
    (coherentIso.compExtensionProperty_of_quasicategory C)

end SSet
