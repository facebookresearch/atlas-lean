/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreRelativeEquivalencePrisms
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ChangingBaseFibreWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown

/-!
# Actual transport of fixed-boundary functor equivalence moduli

The canonical point-choice fibre is identified with the fibre of the original
restriction map. All actions remain the existing source-pair, target and
coefficient maps. Weakness follows from genuine original weak core square
legs and the canonical changing-base fibre theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
  HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Subcomplex

/-- Canonical strict-fibre actions are weak from the actual weak total/base square and fibrations. -/
theorem mapFiber_realizationWeak {X Y X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ p' = p ≫ g) [Fibration p] [Fibration p']
    (hf : realizationWeakEquivalences f) (hg : realizationWeakEquivalences g)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌} (hy : g.app (op ⦋0⦌) y = y') :
    realizationWeakEquivalences (mapFiber f g h hy) := by
  let a : (Δ[0] : SSet.{u}) ⟶ Y := const y
  let a' : (Δ[0] : SSet.{u}) ⟶ Y' := const y'
  have ha : a ≫ g = a' := by
    dsimp only [a, a']
    rw [const_comp, hy]
  let φ := CategoryTheory.Limits.PullbackFibreBaseChange.fibreMapTo f p p' g h.symm a a' ha
  have hφ : realizationWeakEquivalences φ :=
    ChangingBaseFibreWeakComparison.fibreMapTo_weak f p p' g h.symm hf hg a a' ha
  let e₀ := (fiber_isPullback p y).isoPullback
  let e₁ := (fiber_isPullback p' y').isoPullback
  let e : Arrow.mk (mapFiber f g h hy) ≅ Arrow.mk φ := Arrow.isoMk e₀ e₁ (by
    change e₀.hom ≫ φ = mapFiber f g h hy ≫ e₁.hom
    apply pullback.hom_ext
    · dsimp only [φ, e₀, e₁, a, a']
      simp only [Category.assoc,
        CategoryTheory.Limits.PullbackFibreBaseChange.fibreMapTo_fst,
        IsPullback.isoPullback_hom_fst, mapFiber_ι]
      simpa only [Category.assoc] using ((fiber_isPullback p y).isoPullback_hom_fst =≫ f)
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _)
  exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mpr hφ

end SSet.Subcomplex

namespace SSet.FunctorCore.Extension.RelativeEquivalence

variable {A₀ A Q K : SSet.{u}}

/-- The original core coordinate lifts into the raw restriction fibre at the actual family point. -/
def pointRestrictionHom (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointChoice i α k ⟶ (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k) : SSet.{u}) :=
  Subcomplex.lift (pointChoiceInclusion i α k ≫ functorProjection i α) (by
    rw [Subcomplex.range_le_fiber_iff, Category.assoc, projection_square,
      ← Category.assoc, pointChoice_coefficient, const_comp])

/-- The canonical raw-fibre comparison retains the whole original core coordinate. -/
@[reassoc]
theorem pointRestrictionHom_inclusion (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointRestrictionHom i α k ≫ (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι =
      pointChoiceInclusion i α k ≫ functorProjection i α :=
  Subcomplex.lift_ι _ _

/-- The actual raw-fibre inclusion and constant coefficient form the original chosen pullback lift. -/
def pointRestrictionExtension (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k) : SSet.{u}) ⟶ Extension.object i α :=
  pullback.lift (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι (const k) (by
    rw [Subcomplex.fiber_ι_comp, const_comp])

/-- The raw-fibre pullback lift retains its original core leg. -/
@[reassoc]
theorem pointRestrictionExtension_fst (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointRestrictionExtension i α k ≫ functorProjection i α =
      (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι :=
  pullback.lift_fst _ _ _

/-- The raw-fibre pullback lift retains its actual coefficient in all degrees. -/
@[reassoc]
theorem pointRestrictionExtension_snd (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointRestrictionExtension i α k ≫ coefficientProjection i α = const k :=
  pullback.lift_snd _ _ _

/-- The same raw restriction fibre lifts back into the supplied original coefficient fibre. -/
def pointRestrictionInv (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k) : SSet.{u}) ⟶ pointChoice i α k :=
  Subcomplex.lift (pointRestrictionExtension i α k)
    ((Subcomplex.range_le_fiber_iff _ _ _).mpr (pointRestrictionExtension_snd i α k))

/-- The inverse retains the actual original pullback lift under the coefficient-fibre inclusion. -/
@[reassoc]
theorem pointRestrictionInv_inclusion (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointRestrictionInv i α k ≫ pointChoiceInclusion i α k = pointRestrictionExtension i α k :=
  Subcomplex.lift_ι _ _

/-- Coefficient choices and raw restriction fibres agree by the SAME canonical maps and both legs. -/
def pointRestrictionIso (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    pointChoice i α k ≅ (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k) : SSet.{u}) where
  hom := pointRestrictionHom i α k
  inv := pointRestrictionInv i α k
  hom_inv_id := by
    apply (cancel_mono (pointChoiceInclusion i α k)).mp
    apply pullback.hom_ext
    · have h : (pointRestrictionHom i α k ≫ pointRestrictionInv i α k) ≫
          pointChoiceInclusion i α k ≫ functorProjection i α =
            pointChoiceInclusion i α k ≫ functorProjection i α := by
        simp only [Category.assoc]
        rw [pointRestrictionInv_inclusion_assoc, pointRestrictionExtension_fst,
          pointRestrictionHom_inclusion]
      simpa only [Category.assoc, functorProjection, Category.id_comp] using h
    · have h : (pointRestrictionHom i α k ≫ pointRestrictionInv i α k) ≫
          pointChoiceInclusion i α k ≫ coefficientProjection i α =
            pointChoiceInclusion i α k ≫ coefficientProjection i α := by
        simp only [Category.assoc, pointChoice_coefficient, comp_const]
      simpa only [Category.assoc, coefficientProjection, Category.id_comp] using h
  inv_hom_id := by
    apply (cancel_mono (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι).mp
    rw [Category.assoc, pointRestrictionHom_inclusion, ← Category.assoc,
      pointRestrictionInv_inclusion, pointRestrictionExtension_fst, Category.id_comp]

/-- The actual isomorphism hom retains the original first projection. -/
@[reassoc]
theorem pointRestrictionIso_hom_inclusion (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (pointRestrictionIso i α k).hom ≫
        (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι =
      pointChoiceInclusion i α k ≫ functorProjection i α :=
  pointRestrictionHom_inclusion i α k

variable {B₀ B Q' L : SSet.{u}}

/-- The actual coefficient square determines the original raw boundary vertex square. -/
theorem boundaryVertex_square (u₀ : A₀ ⟶ B₀) (g : Q ⟶ Q')
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    (FunctorCore.mapBoth u₀ g).app (op ⦋0⦌) (α.app (op ⦋0⦌) k) = β.app (op ⦋0⦌) l := by
  have h := congrArg (fun f => f.app (op ⦋0⦌) k) hc
  change (FunctorCore.mapBoth u₀ g).app (op ⦋0⦌) (α.app (op ⦋0⦌) k) =
    β.app (op ⦋0⦌) (c.app (op ⦋0⦌) k) at h
  rwa [hl] at h

/-- Whole point-fibre transport agrees with the canonical raw restriction-fibre action. -/
theorem pointRestrictionIso_naturality (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    pointMap i j u₀ u₁ g h α β c hc k l hl ≫ (pointRestrictionIso i β l).hom =
      (pointRestrictionIso j α k).hom ≫
        Subcomplex.mapFiber (FunctorCore.mapBoth u₁ g) (FunctorCore.mapBoth u₀ g)
          (restriction_square i j u₀ u₁ g h).symm (boundaryVertex_square u₀ g α β c hc k l hl) := by
  apply (cancel_mono (Subcomplex.fiber (restriction i Q') (β.app (op ⦋0⦌) l)).ι).mp
  simp only [Category.assoc, pointRestrictionIso_hom_inclusion, pointMap_inclusion_assoc,
    Subcomplex.mapFiber_ι, map_fst]
  simpa only [Category.assoc] using
    (pointRestrictionIso_hom_inclusion j α k =≫ FunctorCore.mapBoth u₁ g).symm

/-- The literal point transport is weak under genuine source-pair/target equivalences, for arbitrary coefficients. -/
theorem pointMap_realizationWeak_of_comparison (i : A₀ ⟶ A) (j : B₀ ⟶ B) [Mono i] [Mono j]
    [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (hu₀ : categoricalEquivalences u₀) (hu₁ : categoricalEquivalences u₁)
    (hg : categoricalEquivalences g)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    realizationWeakEquivalences (pointMap i j u₀ u₁ g h α β c hc k l hl) := by
  let _ : Fibration (restriction j Q) := restriction_fibration j Q
  let _ : Fibration (restriction i Q') := restriction_fibration i Q'
  have hraw := Subcomplex.mapFiber_realizationWeak (restriction j Q) (restriction i Q')
    (FunctorCore.mapBoth u₁ g) (FunctorCore.mapBoth u₀ g) (restriction_square i j u₀ u₁ g h).symm
    (FunctorCore.mapBoth_realizationWeak u₁ g hu₁ hg)
    (FunctorCore.mapBoth_realizationWeak u₀ g hu₀ hg) (boundaryVertex_square u₀ g α β c hc k l hl)
  have htarget : realizationWeakEquivalences (pointRestrictionIso i β l).hom :=
    realizationWeakEquivalences.of_isIso _
  have hsource : realizationWeakEquivalences (pointRestrictionIso j α k).hom :=
    realizationWeakEquivalences.of_isIso _
  apply realizationWeakEquivalences.of_postcomp _ (pointRestrictionIso i β l).hom htarget
  rw [pointRestrictionIso_naturality]
  exact realizationWeakEquivalences.comp_mem _ _ hsource hraw

/-- The actual endpoint vertex is natural for the SAME tensor map on both components. -/
theorem endpointVertex_map {X Y : SSet.{u}} (w : X ⟶ Y) (x y : X _⦋0⦌) :
    (w ⊗ₘ w).app (op ⦋0⦌) (endpointVertex x y) =
      endpointVertex (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) := by
  rw [endpointVertex, ← yonedaEquiv_comp, endpointVertex]
  apply congrArg yonedaEquiv
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst, lift_fst,
      yonedaEquiv_symm_comp]
  · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd, lift_snd,
      yonedaEquiv_symm_comp]

/-- The SAME core-path endpoint map keeps both complete original endpoint squares. -/
theorem endpoint_naturality (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l) :
    (FunctorCore.functor (Δ[1] : SSet.{u})).map w ≫ endpoint i β l =
      endpoint j α k ≫ (w ⊗ₘ w) := by
  have hpair : (ihom (Δ[1] : SSet.{u})).map w ≫ evalPair = evalPair ≫ (w ⊗ₘ w) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, evalPair_fst, tensorHom_fst, evalPair_fst_assoc,
        pathSpace_map_eval₀]
    · simp only [Category.assoc, evalPair_snd, tensorHom_snd, evalPair_snd_assoc,
        pathSpace_map_eval₁]
  calc
    _ = (core (pathSpace (pointChoice j α k))).ι ≫
        ((ihom (Δ[1] : SSet.{u})).map w ≫ evalPair) := by
      rw [endpoint, ← Category.assoc, FunctorCore.map_inclusion, Category.assoc]
    _ = _ := by rw [hpair, endpoint, Category.assoc]

/-- Every original point-fibre map induces the canonical whole endpoint-fibre map. -/
def map (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l)
    (x y : pointChoice j α k _⦋0⦌) :
    object j α k x y ⟶ object i β l (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) :=
  Subcomplex.mapFiber ((FunctorCore.functor (Δ[1] : SSet.{u})).map w) (w ⊗ₘ w)
    (endpoint_naturality i j α β k l w) (endpointVertex_map w x y)

/-- The whole moduli map retains the original core-path action under the actual fibre inclusion. -/
@[reassoc]
theorem map_inclusion (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l)
    (x y : pointChoice j α k _⦋0⦌) :
    map i j α β k l w x y ≫ inclusion i β l (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) =
      inclusion j α k x y ≫ (FunctorCore.functor (Δ[1] : SSet.{u})).map w :=
  Subcomplex.mapFiber_ι _ _ _ _

/-- Identity acts as identity on the SAME whole moduli object. -/
theorem map_id (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (x y : pointChoice i α k _⦋0⦌) : map i i α α k k (𝟙 _) x y = 𝟙 (object i α k x y) := by
  apply (cancel_mono (inclusion i α k x y)).mp
  have h := map_inclusion i i α α k k (𝟙 _) x y
  have hmap := (FunctorCore.functor (Δ[1] : SSet.{u})).map_id (pointChoice i α k)
  have hright : inclusion i α k x y ≫
      (FunctorCore.functor (Δ[1] : SSet.{u})).map (𝟙 (pointChoice i α k)) = inclusion i α k x y := by
    rw [hmap, Category.comp_id]
  simpa only [NatTrans.id_app, types_id_apply, Category.id_comp] using h.trans hright

/-- Composition retains the original point maps and every simplicial degree of the moduli action. -/
theorem map_comp {C₀ C Q'' M : SSet.{u}}
    (i : A₀ ⟶ A) (j : B₀ ⟶ B) (t : C₀ ⟶ C)
    (α : K ⟶ (FunctorCore.functor C₀).obj Q) (β : L ⟶ (FunctorCore.functor B₀).obj Q')
    (γ : M ⟶ (FunctorCore.functor A₀).obj Q'')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (m : M _⦋0⦌)
    (w : pointChoice t α k ⟶ pointChoice j β l) (v : pointChoice j β l ⟶ pointChoice i γ m)
    (x y : pointChoice t α k _⦋0⦌) :
    map j t α β k l w x y ≫ map i j β γ l m v (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) =
      map i t α γ k m (w ≫ v) x y := by
  apply (cancel_mono (inclusion i γ m ((w ≫ v).app (op ⦋0⦌) x)
    ((w ≫ v).app (op ⦋0⦌) y))).mp
  calc
    _ = map j t α β k l w x y ≫
        (map i j β γ l m v (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) ≫
          inclusion i γ m (v.app (op ⦋0⦌) (w.app (op ⦋0⦌) x))
            (v.app (op ⦋0⦌) (w.app (op ⦋0⦌) y))) := by
      simp only [Category.assoc, NatTrans.comp_app, types_comp_apply]
    _ = _ := by
      rw [map_inclusion, ← Category.assoc, map_inclusion, Category.assoc, ← Functor.map_comp]
      exact (map_inclusion i t α γ k m (w ≫ v) x y).symm

private theorem corePathMap_realizationWeak {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (w : X ⟶ Y) (hw : realizationWeakEquivalences w) :
    realizationWeakEquivalences ((FunctorCore.functor (Δ[1] : SSet.{u})).map w) := by
  let _ : WeakEquivalence w := (weakEquivalence_iff w).mpr hw
  let hPP := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := SSet.{u})
  have hpath : WeakEquivalence ((ihom (Δ[1] : SSet.{u})).map w) :=
    hPP.ihom_weakEquivalence_of_fibrant (Δ[1] : SSet.{u}) w
  have hwpath : realizationWeakEquivalences ((ihom (Δ[1] : SSet.{u})).map w) :=
    (weakEquivalence_iff _).mp hpath
  have hsource : realizationWeakEquivalences (core (pathSpace X)).ι := by
    rw [← corePathIso_hom]
    exact realizationWeakEquivalences.of_isIso _
  have htarget : realizationWeakEquivalences (core (pathSpace Y)).ι := by
    rw [← corePathIso_hom]
    exact realizationWeakEquivalences.of_isIso _
  apply realizationWeakEquivalences.of_postcomp _ _ htarget
  rw [FunctorCore.map_inclusion]
  exact realizationWeakEquivalences.comp_mem _ _ hsource hwpath

private theorem tensorPairMap_realizationWeak {X Y : SSet.{u}}
    (w : X ⟶ Y) (hw : realizationWeakEquivalences w) : realizationWeakEquivalences (w ⊗ₘ w) := by
  let _ : WeakEquivalence w := (weakEquivalence_iff w).mpr hw
  let hPP := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := SSet.{u})
  have hpair : WeakEquivalence (w ⊗ₘ w) :=
    hPP.tensorHom_weakEquivalence w w
  exact (weakEquivalence_iff _).mp hpair

/-- The SAME whole moduli action is weak from an actual weak original point-fibre map. -/
theorem map_realizationWeak (i : A₀ ⟶ A) (j : B₀ ⟶ B) [Mono i] [Mono j]
    [Quasicategory Q] [Quasicategory Q']
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l)
    (hw : realizationWeakEquivalences w) (x y : pointChoice j α k _⦋0⦌) :
    realizationWeakEquivalences (map i j α β k l w x y) := by
  let _ : KanComplex (pointChoice j α k) := pointChoice_isKan j α k
  let _ : KanComplex (pointChoice i β l) := pointChoice_isKan i β l
  let _ : Fibration (endpoint j α k) := endpoint_fibration j α k
  let _ : Fibration (endpoint i β l) := endpoint_fibration i β l
  exact Subcomplex.mapFiber_realizationWeak (endpoint j α k) (endpoint i β l)
    ((FunctorCore.functor (Δ[1] : SSet.{u})).map w) (w ⊗ₘ w) (endpoint_naturality i j α β k l w)
    (corePathMap_realizationWeak w hw) (tensorPairMap_realizationWeak w hw) (endpointVertex_map w x y)

/-- The SAME whole moduli action belongs to the structural Kan weak class. -/
theorem map_mem_W (i : A₀ ⟶ A) (j : B₀ ⟶ B) [Mono i] [Mono j]
    [Quasicategory Q] [Quasicategory Q']
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l)
    (hw : realizationWeakEquivalences w) (x y : pointChoice j α k _⦋0⦌) :
    KanComplex.W (map i j α β k l w x y) := by
  let _ : KanComplex (object j α k x y) := object_isKan j α k x y
  let _ : KanComplex (object i β l (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y)) :=
    object_isKan i β l _ _
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr (map_realizationWeak i j α β k l w hw x y)

/-- Every full path family retains its literal original point-fibre target action. -/
theorem family_map {T : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (k : K _⦋0⦌) (l : L _⦋0⦌) (w : pointChoice j α k ⟶ pointChoice i β l)
    (x y : pointChoice j α k _⦋0⦌) (f : T ⟶ object j α k x y) :
    family i β l (w.app (op ⦋0⦌) x) (w.app (op ⦋0⦌) y) (f ≫ map i j α β k l w x y) =
      family j α k x y f ≫ w := by
  unfold family
  simp only [Category.assoc]
  rw [map_inclusion_assoc]
  calc
    _ = uncurry ((f ≫ inclusion j α k x y) ≫
        ((core (pathSpace (pointChoice j α k))).ι ≫ (ihom (Δ[1] : SSet.{u})).map w)) := by
      simpa only [Category.assoc, FunctorCore.functor, Functor.comp_map, pathSpace] using congrArg
        (fun z => uncurry ((f ≫ inclusion j α k x y) ≫ z))
        (FunctorCore.map_inclusion (K := (Δ[1] : SSet.{u})) w)
    _ = _ := by
      simpa only [Category.assoc] using
        (uncurry_natural_right (f ≫ inclusion j α k x y ≫
          (core (pathSpace (pointChoice j α k))).ι) w)

/-- The actual presentation action uses the SAME original source-pair/target/coefficient point map. -/
def presentationMap (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l)
    (x y : pointChoice j α k _⦋0⦌) :
    object j α k x y ⟶ object i β l
      ((pointMap i j u₀ u₁ g h α β c hc k l hl).app (op ⦋0⦌) x)
      ((pointMap i j u₀ u₁ g h α β c hc k l hl).app (op ⦋0⦌) y) :=
  map i j α β k l (pointMap i j u₀ u₁ g h α β c hc k l hl) x y

/-- Genuine presentation equivalences act weakly on the SAME whole relative-equivalence moduli. -/
theorem presentationMap_mem_W (i : A₀ ⟶ A) (j : B₀ ⟶ B) [Mono i] [Mono j]
    [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (hu₀ : categoricalEquivalences u₀) (hu₁ : categoricalEquivalences u₁)
    (hg : categoricalEquivalences g)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l)
    (x y : pointChoice j α k _⦋0⦌) :
    KanComplex.W (presentationMap i j u₀ u₁ g h α β c hc k l hl x y) :=
  map_mem_W i j α β k l _
    (pointMap_realizationWeak_of_comparison i j u₀ u₁ g h hu₀ hu₁ hg α β c hc k l hl) x y

/-- The actual whole prism action retains both original source and target maps in every parameter. -/
theorem actualPrism_presentationMap {T : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q')
    (c : K ⟶ L) (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l)
    (x y : pointChoice j α k _⦋0⦌) (f : T ⟶ object j α k x y) :
    actualPrism i β l ((pointMap i j u₀ u₁ g h α β c hc k l hl).app (op ⦋0⦌) x)
      ((pointMap i j u₀ u₁ g h α β c hc k l hl).app (op ⦋0⦌) y)
      (f ≫ presentationMap i j u₀ u₁ g h α β c hc k l hl x y) =
        u₁ ▷ ((Δ[1] : SSet.{u}) ⊗ T) ≫ actualPrism j α k x y f ≫ g := by
  unfold actualPrism presentationMap
  rw [family_map]
  exact pointPrism_map i j u₀ u₁ g h α β c hc k l hl _

/-- The canonical inverse point-fibre comparison retains the original complete core coordinate. -/
@[reassoc]
theorem pointRestrictionIso_inv_core (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    (pointRestrictionIso i α k).inv ≫ pointChoiceInclusion i α k ≫ functorProjection i α =
      (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι := by
  change pointRestrictionInv i α k ≫ pointChoiceInclusion i α k ≫ functorProjection i α = _
  rw [pointRestrictionInv_inclusion_assoc, pointRestrictionExtension_fst]

/-- Actual agreement of original boundary vertices identifies two independent coefficient presentations. -/
def pointCoefficientIso (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (h : α.app (op ⦋0⦌) k = β.app (op ⦋0⦌) l) :
    pointChoice i α k ≅ pointChoice i β l :=
  pointRestrictionIso i α k ≪≫
    Subcomplex.eqToIso (congrArg (Subcomplex.fiber (restriction i Q)) h) ≪≫
      (pointRestrictionIso i β l).symm

/-- The independent coefficient-presentation comparison retains both actual original core legs. -/
@[reassoc]
theorem pointCoefficientIso_core (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (h : α.app (op ⦋0⦌) k = β.app (op ⦋0⦌) l) :
    (pointCoefficientIso i α β k l h).hom ≫ pointChoiceInclusion i β l ≫ functorProjection i β =
      pointChoiceInclusion i α k ≫ functorProjection i α := by
  let hs := congrArg (Subcomplex.fiber (restriction i Q)) h
  have hι : (Subcomplex.eqToIso hs).hom ≫
      (Subcomplex.fiber (restriction i Q) (β.app (op ⦋0⦌) l)).ι =
        (Subcomplex.fiber (restriction i Q) (α.app (op ⦋0⦌) k)).ι :=
    Subcomplex.homOfLE_ι hs.le
  change (pointRestrictionIso i α k).hom ≫ (Subcomplex.eqToIso hs).hom ≫
    (pointRestrictionIso i β l).inv ≫ pointChoiceInclusion i β l ≫ functorProjection i β = _
  rw [pointRestrictionIso_inv_core, hι, pointRestrictionIso_hom_inclusion]

/-- Independent coefficient presentations retain the SAME whole original evaluator and marked prism. -/
theorem pointCoefficientIso_prism {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (h : α.app (op ⦋0⦌) k = β.app (op ⦋0⦌) l)
    (f : T ⟶ pointChoice i α k) :
    pointPrism i β l (f ≫ (pointCoefficientIso i α β k l h).hom) = pointPrism i α k f := by
  apply curry_injective
  simp only [pointPrism, prism_curry, Category.assoc]
  rw [pointCoefficientIso_core_assoc]

/-- The SAME moduli action between independent coefficient choices is weak without Kan coefficients. -/
theorem coefficientPresentation_mem_W (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (h : α.app (op ⦋0⦌) k = β.app (op ⦋0⦌) l)
    (x y : pointChoice i α k _⦋0⦌) :
    KanComplex.W (map i i α β k l (pointCoefficientIso i α β k l h).hom x y) :=
  map_mem_W i i α β k l _ (realizationWeakEquivalences.of_isIso _) x y

/-- The independent coefficient moduli comparison retains the full original A × Δ[1] × T prism. -/
theorem actualPrism_coefficientPresentation {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (β : L ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (h : α.app (op ⦋0⦌) k = β.app (op ⦋0⦌) l)
    (x y : pointChoice i α k _⦋0⦌) (f : T ⟶ object i α k x y) :
    actualPrism i β l ((pointCoefficientIso i α β k l h).hom.app (op ⦋0⦌) x)
      ((pointCoefficientIso i α β k l h).hom.app (op ⦋0⦌) y)
      (f ≫ map i i α β k l (pointCoefficientIso i α β k l h).hom x y) =
        actualPrism i α k x y f := by
  unfold actualPrism
  rw [family_map, pointCoefficientIso_prism]

end SSet.FunctorCore.Extension.RelativeEquivalence
