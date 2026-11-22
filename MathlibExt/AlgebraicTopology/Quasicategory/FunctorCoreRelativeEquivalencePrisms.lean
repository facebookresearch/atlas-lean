/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreExtensionPointChoices
import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseCore
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace

/-!
# Original functor equivalences with a fixed coefficient boundary

The endpoint fibre uses the canonical core path object of the original
coefficient fibre. Its paths keep the supplied coefficient point fixed.
Every simplicial parameter retains the whole original marked prism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
  HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.Extension.RelativeEquivalence

variable {A₀ A Q K : SSet.{u}}

/-- The actual core-path inclusion is the canonical top-core isomorphism for a Kan object. -/
def corePathIso (X : SSet.{u}) [KanComplex X] :
    (FunctorCore.functor (Δ[1] : SSet.{u})).obj X ≅ pathSpace X :=
  Subcomplex.eqToIso (core_eq_top_of_kanComplex (pathSpace X)) ≪≫ Subcomplex.topIso _

/-- The canonical isomorphism retains the literal original core inclusion. -/
theorem corePathIso_hom (X : SSet.{u}) [KanComplex X] :
    (corePathIso X).hom = (core (pathSpace X)).ι :=
  Subcomplex.homOfLE_ι (core_eq_top_of_kanComplex (pathSpace X)).le

/-- The inverse cancels the SAME whole core inclusion. -/
@[reassoc]
theorem corePathIso_inv_inclusion (X : SSet.{u}) [KanComplex X] :
    (corePathIso X).inv ≫ (core (pathSpace X)).ι = 𝟙 (pathSpace X) := by
  rw [← corePathIso_hom, Iso.inv_hom_id]

/-- The endpoint vertex uses the actual Cartesian pairing, with its canonical Yoneda name. -/
def endpointVertex {X : SSet.{u}} (x y : X _⦋0⦌) : (X ⊗ X) _⦋0⦌ :=
  yonedaEquiv (lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))

/-- The first component of the chosen endpoint vertex is the supplied original point. -/
theorem endpointVertex_fst {X : SSet.{u}} (x y : X _⦋0⦌) :
    (fst X X).app (op ⦋0⦌) (endpointVertex x y) = x := by
  rw [endpointVertex, ← yonedaEquiv_comp, lift_fst, Equiv.apply_symm_apply]

/-- The second component of the chosen endpoint vertex is the supplied original point. -/
theorem endpointVertex_snd {X : SSet.{u}} (x y : X _⦋0⦌) :
    (snd X X).app (op ⦋0⦌) (endpointVertex x y) = y := by
  rw [endpointVertex, ← yonedaEquiv_comp, lift_snd, Equiv.apply_symm_apply]

/-- Both original path endpoints in the specified coefficient fibre. -/
def endpoint (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (FunctorCore.functor (Δ[1] : SSet.{u})).obj (pointChoice i α k) ⟶
      pointChoice i α k ⊗ pointChoice i α k :=
  (core (pathSpace (pointChoice i α k))).ι ≫ evalPair

/-- The full moduli object is the canonical endpoint fibre at the two actual extensions. -/
abbrev object (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) : SSet.{u} :=
  (Subcomplex.fiber (endpoint i α k) (endpointVertex x y) : SSet.{u})

/-- The original endpoint-fibre inclusion. -/
abbrev inclusion (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) :
    object i α k x y ⟶ (FunctorCore.functor (Δ[1] : SSet.{u})).obj (pointChoice i α k) :=
  (Subcomplex.fiber (endpoint i α k) (endpointVertex x y)).ι

/-- The actual terminal map of the same endpoint fibre. -/
def projection (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) : object i α k x y ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from _

/-- The existing endpoint fibration applies without a Kan coefficient or source premise. -/
theorem endpoint_fibration (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) : Fibration (endpoint i α k) := by
  let _ : KanComplex (pointChoice i α k) := pointChoice_isKan i α k
  have : IsIso (core (pathSpace (pointChoice i α k))).ι := by
    rw [← corePathIso_hom]
    infer_instance
  unfold endpoint
  infer_instance

/-- Relative equivalences form a genuine Kan space, which can be empty for a mere monomorphism. -/
theorem object_isKan (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) : KanComplex (object i α k x y) := by
  let _ : Fibration (endpoint i α k) := endpoint_fibration i α k
  infer_instance

/-- The whole path family obtained from the SAME core endpoint-fibre inclusion. -/
def family {T : SSet.{u}} (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    (Δ[1] : SSet.{u}) ⊗ T ⟶ pointChoice i α k :=
  uncurry (f ≫ inclusion i α k x y ≫ (core (pathSpace (pointChoice i α k))).ι)

/-- Every whole family has the original constant endpoint pair. -/
theorem family_classifier {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    (f ≫ inclusion i α k x y ≫ (core (pathSpace (pointChoice i α k))).ι) ≫ evalPair =
      const (X := T) (endpointVertex x y) := by
  simp only [Category.assoc]
  change f ≫ inclusion i α k x y ≫ endpoint i α k = _
  rw [Subcomplex.fiber_ι_comp, comp_const]

/-- The original initial-time endpoint is fixed in every parameter degree. -/
theorem family_left {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ family i α k x y f = const x := by
  rw [family, ← comp_eval₀_eq_ι₀_braiding_uncurry]
  have h := family_classifier i α k x y f =≫ fst (pointChoice i α k) (pointChoice i α k)
  simpa only [Category.assoc, evalPair_fst, const_comp, endpointVertex_fst] using h

/-- The original final-time endpoint is fixed in every parameter degree. -/
theorem family_right {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ family i α k x y f = const y := by
  rw [family, ← comp_eval₁_eq_ι₁_braiding_uncurry]
  have h := family_classifier i α k x y f =≫ snd (pointChoice i α k) (pointChoice i α k)
  simpa only [Category.assoc, evalPair_snd, const_comp, endpointVertex_snd] using h

/-- Both actual endpoints recover the original endpoint classifier by ordinary currying. -/
theorem curry_classifier {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (H : (Δ[1] : SSet.{u}) ⊗ T ⟶ pointChoice i α k)
    (h₀ : ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const x)
    (h₁ : ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const y) :
    curry H ≫ evalPair =
      const (X := T) (endpointVertex x y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, evalPair_fst, comp_eval₀_eq_ι₀_braiding_uncurry, uncurry_curry, h₀,
      const_comp, endpointVertex_fst]
  · rw [Category.assoc, evalPair_snd, comp_eval₁_eq_ι₁_braiding_uncurry, uncurry_curry, h₁,
      const_comp, endpointVertex_snd]

/-- The full parameter dictionary is valid even when T and the original sources are not Kan. -/
def parameterEquiv (T : SSet.{u}) (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) :
    (T ⟶ object i α k x y) ≃
      {H : (Δ[1] : SSet.{u}) ⊗ T ⟶ pointChoice i α k //
        ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const x ∧
        ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const y} := by
  let _ : KanComplex (pointChoice i α k) := pointChoice_isKan i α k
  refine {
    toFun := fun f => ⟨family i α k x y f, family_left i α k x y f, family_right i α k x y f⟩
    invFun := fun H => Subcomplex.lift (curry H.val ≫ (corePathIso (pointChoice i α k)).inv)
      ((Subcomplex.range_le_fiber_iff _ _ _).mpr ?_)
    left_inv := ?_
    right_inv := ?_ }
  · simp only [endpoint, Category.assoc, corePathIso_inv_inclusion_assoc]
    exact curry_classifier i α k x y H.val H.property.1 H.property.2
  · intro f
    apply (cancel_mono (inclusion i α k x y)).mp
    apply (cancel_mono (core (pathSpace (pointChoice i α k))).ι).mp
    rw [Subcomplex.lift_ι, Category.assoc, corePathIso_inv_inclusion, Category.comp_id]
    exact curry_uncurry _
  · intro H
    apply Subtype.ext
    change uncurry (Subcomplex.lift _ _ ≫ inclusion i α k x y ≫ _) = H.val
    rw [← Category.assoc, Subcomplex.lift_ι, Category.assoc, corePathIso_inv_inclusion, Category.comp_id,
      uncurry_curry]

/-- Every actual parameter map retains the SAME full path family. -/
theorem family_precomp {T T' : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (a : T' ⟶ T) (f : T ⟶ object i α k x y) :
    family i α k x y (a ≫ f) = (Δ[1] : SSet.{u}) ◁ a ≫ family i α k x y f := by
  unfold family
  rw [Category.assoc, uncurry_natural_left]

/-- The original point prism is marked and has its supplied stationary boundary. -/
abbrev PointAdmissible {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) (G : A ⊗ T ⟶ Q) : Prop :=
  Admissible i α (G, const (X := T) k)

/-- The original marked prism gives its actual lift through the supplied coefficient fibre. -/
def pointFromPrism {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) (G : A ⊗ T ⟶ Q)
    (hG : PointAdmissible i α k G) : T ⟶ pointChoice i α k :=
  Subcomplex.lift (fromPrism i α ⟨(G, const k), hG⟩)
    ((Subcomplex.range_le_fiber_iff _ _ _).mpr (fromPrism_snd i α _))

/-- The lifted point prism retains the SAME original pullback lift. -/
@[reassoc]
theorem pointFromPrism_inclusion {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) (G : A ⊗ T ⟶ Q)
    (hG : PointAdmissible i α k G) :
    pointFromPrism i α k G hG ≫ pointChoiceInclusion i α k =
      fromPrism i α ⟨(G, const k), hG⟩ :=
  Subcomplex.lift_ι _ _

/-- The full original core coordinate of the inverse is ordinary curry of the supplied prism. -/
theorem pointFromPrism_core {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) (G : A ⊗ T ⟶ Q)
    (hG : PointAdmissible i α k G) :
    pointFromPrism i α k G hG ≫ pointChoiceInclusion i α k ≫ functorProjection i α ≫
      (core ((ihom A).obj Q)).ι = curry G := by
  rw [pointFromPrism_inclusion_assoc, ← Category.assoc, fromPrism_fst, Subcomplex.lift_ι]

/-- Every original marked stationary prism is exactly a map into the SAME coefficient fibre. -/
def pointPrismEquiv (T : SSet.{u}) (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (T ⟶ pointChoice i α k) ≃ {G : A ⊗ T ⟶ Q // PointAdmissible i α k G} where
  toFun f := ⟨pointPrism i α k f,
    (toPrism i α (f ≫ pointChoiceInclusion i α k)).property.1, pointPrism_boundary i α k f⟩
  invFun G := pointFromPrism i α k G.val G.property
  left_inv f := by
    apply (cancel_mono (pointChoiceInclusion i α k)).mp
    apply pullback.hom_ext
    · apply (cancel_mono (core ((ihom A).obj Q)).ι).mp
      simpa only [Category.assoc, functorProjection, pointPrism] using
        (pointFromPrism_core i α k _ _).trans (prism_curry i α (f ≫ pointChoiceInclusion i α k))
    · simp only [Category.assoc, pointChoice_coefficient, comp_const]
  right_inv G := by
    apply Subtype.ext
    apply curry_injective
    change curry (prism i α (pointFromPrism i α k G.val G.property ≫ pointChoiceInclusion i α k)) = _
    rw [prism_curry]
    exact pointFromPrism_core i α k G.val G.property

/-- The original evaluator reflects equality of maps into a fixed coefficient fibre. -/
theorem pointPrism_injective {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    Function.Injective (pointPrism (T := T) i α k) := by
  intro f g h
  apply (pointPrismEquiv T i α k).injective
  exact Subtype.ext h

/-- The point prism retains every original parameter precomposition. -/
theorem pointPrism_precomp {T T' : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (a : T' ⟶ T) (f : T ⟶ pointChoice i α k) :
    pointPrism i α k (a ≫ f) = A ◁ a ≫ pointPrism i α k f := by
  unfold pointPrism prism
  simp only [Category.assoc]
  exact uncurry_natural_left _ _

/-- A whole original evaluator endpoint is exactly the SAME fixed point-fibre endpoint. -/
theorem pointPrism_endpoint_iff {T T' : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (a : T' ⟶ T) (f : T ⟶ pointChoice i α k) (z : pointChoice i α k _⦋0⦌) :
    A ◁ a ≫ pointPrism i α k f = pointPrism i α k (const z) ↔ a ≫ f = const z := by
  rw [← pointPrism_precomp]
  exact ⟨fun h => pointPrism_injective (T := T') i α k h,
    fun h => congrArg (pointPrism i α k) h⟩

/-- The full A × Δ[1] × T prism uses the literal original coefficient-fibre evaluator. -/
def actualPrism {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    A ⊗ ((Δ[1] : SSet.{u}) ⊗ T) ⟶ Q :=
  pointPrism i α k (family i α k x y f)

/-- The actual prism keeps the prescribed original boundary constant in time and the whole parameter. -/
theorem actualPrism_boundary {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    i ▷ ((Δ[1] : SSet.{u}) ⊗ T) ≫ actualPrism i α k x y f =
      uncurry (const (X := (Δ[1] : SSet.{u}) ⊗ T) k ≫ α ≫ (core ((ihom A₀).obj Q)).ι) :=
  pointPrism_boundary i α k _

/-- The whole original core marking is retained, including arbitrary higher parameters. -/
theorem actualPrism_marked {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    Subcomplex.range (curry (actualPrism i α k x y f)) ≤ core ((ihom A).obj Q) :=
  (toPrism i α (family i α k x y f ≫ pointChoiceInclusion i α k)).property.1

/-- The full original prism keeps its actual initial extension in every parameter degree. -/
theorem actualPrism_left {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    A ◁ (ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ actualPrism i α k x y f =
      pointPrism i α k (const (X := T) x) := by
  rw [actualPrism, ← pointPrism_precomp, Category.assoc, family_left]

/-- The full original prism keeps its actual final extension in every parameter degree. -/
theorem actualPrism_right {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    A ◁ (ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ actualPrism i α k x y f =
      pointPrism i α k (const (X := T) y) := by
  rw [actualPrism, ← pointPrism_precomp, Category.assoc, family_right]

/-- Both original endpoints and the SAME whole stationary core marking characterize admissible prisms. -/
abbrev PrismAdmissible {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (G : A ⊗ ((Δ[1] : SSet.{u}) ⊗ T) ⟶ Q) : Prop :=
  PointAdmissible i α k G ∧
    A ◁ (ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ G = pointPrism i α k (const (X := T) x) ∧
    A ◁ (ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ G = pointPrism i α k (const (X := T) y)

/-- All original A × Δ[1] × T prisms, including their endpoints and marking, form the SAME moduli maps. -/
def prismParameterEquiv (T : SSet.{u}) (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) :
    (T ⟶ object i α k x y) ≃
      {G : A ⊗ ((Δ[1] : SSet.{u}) ⊗ T) ⟶ Q // PrismAdmissible i α k x y G} := by
  let e := pointPrismEquiv ((Δ[1] : SSet.{u}) ⊗ T) i α k
  let p := fun H : (Δ[1] : SSet.{u}) ⊗ T ⟶ pointChoice i α k =>
    ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const x ∧
      ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom ≫ H = const y
  let q := fun G : A ⊗ ((Δ[1] : SSet.{u}) ⊗ T) ⟶ Q =>
    A ◁ (ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ G = pointPrism i α k (const (X := T) x) ∧
      A ◁ (ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom) ≫ G = pointPrism i α k (const (X := T) y)
  have hp : ∀ H, p H ↔ q (e H).val := by
    intro H
    change p H ↔ q (pointPrism i α k H)
    dsimp only [p, q]
    rw [pointPrism_endpoint_iff, pointPrism_endpoint_iff]
    simp only [Category.assoc]
  exact (parameterEquiv T i α k x y).trans
    ((e.subtypeEquiv hp).trans (Equiv.subtypeSubtypeEquivSubtypeInter
      (PointAdmissible i α k) q))

/-- The full prism dictionary keeps the literal original evaluator as its forward map. -/
theorem prismParameterEquiv_val {T : SSet.{u}} (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    ((prismParameterEquiv T i α k x y) f).val = actualPrism i α k x y f := rfl

end SSet.FunctorCore.Extension.RelativeEquivalence
