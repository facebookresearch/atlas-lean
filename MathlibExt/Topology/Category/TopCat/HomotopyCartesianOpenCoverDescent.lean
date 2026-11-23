/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparison
public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparisonNaturality
public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackComparisonFibration
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberRestriction
public import MathlibExt.Topology.Category.TopCat.OpenCoverHomotopyPushout
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberwiseDetection
import MathlibExt.Topology.Category.TopCat.HomotopyPullbackMappingPath
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Factorization
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Stability
import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
import Mathlib.AlgebraicTopology.ModelCategory.Over
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LeftProper
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono

/-!
# Actual comparisons for homotopy-cartesian restriction squares

A strict commutative square has a canonical map to the compact-open
homotopy pullback, using the constant path at its common base coordinate.
The comparison retains its two given maps. Its strict-pullback case is weak
when the original projection is an actual fibration.

The two-open-set quasifibration criterion uses the actual restrictions and
their constant-path comparisons. Subordinate singular excision, minimal
fibration gluing, actual global-total extension and the point-fiber map
identity prove the global comparison weak from the three local comparisons.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat


end TopCat

namespace SSet

open CartesianMonoidalCategory Opposite
open scoped SSet.modelCategoryQuillen MonoidalCategory Simplicial

private theorem exists_fibration_span_leg
    {A E F B : SSet.{u}} (i : A ⟶ E) [Mono i] (j : A ⟶ F)
    (hj : trivialCofibrations SSet.{u} j) (p : E ⟶ B) (q : F ⟶ B)
    (comm : i ≫ p = j ≫ q) :
    ∃ (Z : SSet.{u}) (l : E ⟶ Z) (m : F ⟶ Z) (r : Z ⟶ B),
      trivialCofibrations SSet.{u} l ∧ Cofibration m ∧ Fibration r ∧
      l ≫ r = p ∧ m ≫ r = q ∧ i ≫ l = j ≫ m := by
  let _ : Cofibration i := modelCategoryQuillen.cofibration_of_mono i
  obtain ⟨hcj, hwj⟩ := (mem_trivialCofibrations_iff j).mp hj
  let _ : Cofibration j := hcj
  let _ : WeakEquivalence j := hwj
  let t := pushout.desc p q comm
  let d := MorphismProperty.factorizationData (trivialCofibrations SSet.{u})
    (fibrations SSet.{u}) t
  obtain ⟨hcd, hwd⟩ := (mem_trivialCofibrations_iff d.i).mp d.hi
  let _ : Cofibration d.i := hcd
  let _ : WeakEquivalence d.i := hwd
  let _ : Fibration d.p := (HomotopicalAlgebra.fibration_iff _).mpr d.hp
  let l := pushout.inl i j ≫ d.i
  let m := pushout.inr i j ≫ d.i
  refine ⟨d.Z, l, m, d.p, mem_trivialCofibrations l, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · simp only [l, Category.assoc, d.fac, t, pushout.inl_desc]
  · simp only [m, Category.assoc, d.fac, t, pushout.inr_desc]
  · simp only [l, m, ← Category.assoc]
    exact (reassoc_of% (pushout.condition (f := i) (g := j))) d.i

private theorem overObjects_cofibrant {B : SSet.{u}} (X : Over B) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibrations_over_iff]
  exact (isCofibrant_iff_of_isInitial (initial.to X).left
    (initialIsInitial.isInitialObj (G := Over.forget B))).mp inferInstance

private theorem overMk_fibrant {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    IsFibrant (Over.mk p) := by
  let f : Over.mk p ⟶ Over.mk (𝟙 B) := Over.homMk p
  apply (isFibrant_iff_of_isTerminal f Over.mkIdTerminal).mpr
  rw [fibrations_over_iff]
  exact inferInstanceAs (Fibration p)

private abbrev standardCylinderOver {B : SSet.{u}} (X : Over B) : Cylinder X where
  I := Over.mk (fst X.left (Δ[1] : SSet.{u}) ≫ X.hom)
  i₀ := Over.homMk (SSet.modelCategoryQuillen.standardCylinder X.left).i₀ (by simp)
  i₁ := Over.homMk (SSet.modelCategoryQuillen.standardCylinder X.left).i₁ (by simp)
  π := Over.homMk (SSet.modelCategoryQuillen.standardCylinder X.left).π
  weakEquivalence_π := by
    rw [weakEquivalences_over_iff]
    exact (SSet.modelCategoryQuillen.standardCylinder X.left).weakEquivalence_π

private instance standardCylinderOver_good {B : SSet.{u}} (X : Over B) :
    (standardCylinderOver X).IsGood where
  cofibration_i := by
    rw [cofibrations_over_iff, HomotopicalAlgebra.cofibration_iff]
    change Mono (standardCylinderOver X).i.left
    let F := Over.forget B
    let e := PreservesColimitPair.iso F X X
    have he : e.hom ≫ (standardCylinderOver X).i.left =
        (SSet.modelCategoryQuillen.standardCylinder X.left).i := by
      apply coprod.hom_ext
      · simp [e, PreservesColimitPair.iso_hom, coprodComparison,
          F]
        rw [← Over.comp_left, (standardCylinderOver X).toPrecylinder.inl_i]
        rfl
      · simp [e, PreservesColimitPair.iso_hom, coprodComparison,
          F]
        rw [← Over.comp_left, (standardCylinderOver X).toPrecylinder.inr_i]
        rfl
    apply (mono_comp_iff_of_isIso e.hom _).mp
    rw [he]
    exact (SSet.modelCategoryQuillen.cofibration_iff _).mp
      (SSet.modelCategoryQuillen.standardCylinder_isGood X.left).cofibration_i

private def fiberwiseHomotopy_of_overLeftHomotopy
    {B : SSet.{u}} {X Y : Over B} [IsFibrant Y] {f g : X ⟶ Y}
    (h : LeftHomotopyRel f g) : FiberwiseHomotopy X.hom Y.hom f.left g.left := by
  let _ : IsCofibrant X := overObjects_cofibrant X
  let H := h.leftHomotopy (standardCylinderOver X)
  exact
    { hom := Homotopy.mkOfH H.h.left
        (congrArg (fun k => k.left) H.h₀) (congrArg (fun k => k.left) H.h₁)
      over := H.h.w }

private theorem exists_fiberwise_homotopy_inverse
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [Fibration p] [Fibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) [WeakEquivalence f] :
    ∃ g : E' ⟶ E,
      Nonempty (FiberwiseHomotopy p p (f ≫ g) (𝟙 E)) ∧
      Nonempty (FiberwiseHomotopy q q (g ≫ f) (𝟙 E')) := by
  let X := Over.mk p
  let Y := Over.mk q
  let F : X ⟶ Y := Over.homMk f hf
  let _ : WeakEquivalence F := by
    rw [weakEquivalences_over_iff]
    exact inferInstanceAs (WeakEquivalence f)
  let _ : IsFibrant X := overMk_fibrant p
  let _ : IsFibrant Y := overMk_fibrant q
  let _ : IsCofibrant X := overObjects_cofibrant X
  let _ : IsCofibrant Y := overObjects_cofibrant Y
  obtain ⟨G, hFG, hGF⟩ := LeftHomotopyClass.whitehead F
  exact ⟨G.left, ⟨fiberwiseHomotopy_of_overLeftHomotopy hFG⟩,
    ⟨fiberwiseHomotopy_of_overLeftHomotopy hGF⟩⟩

private theorem minimalFibration_isIso_of_weakEquivalence
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (hp : MinimalFibration.IsMinimalFibration p)
    (hq : MinimalFibration.IsMinimalFibration q)
    (f : E ⟶ E') (hf : f ≫ q = p) [WeakEquivalence f] : IsIso f := by
  let _ : Fibration p := hp.1
  let _ : Fibration q := hq.1
  obtain ⟨g, ⟨hfg⟩, ⟨hgf⟩⟩ := exists_fiberwise_homotopy_inverse p q f hf
  exact MinimalFibration.isIso_of_fiberwiseHomotopyEquiv p q hp hq f g hfg hgf

private theorem minimalSubfibration_retraction_weak
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (M : MinimalFibration.MinimalSubfibration p) : WeakEquivalence M.sdr.r := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  exact SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences
    M.sdr.r M.retraction_mem_I_rlp

private theorem minimalSubfibration_retraction_trivialFibration
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (M : MinimalFibration.MinimalSubfibration p) :
    trivialFibrations SSet.{u} M.sdr.r := by
  rw [← cofibrations_rlp, modelCategoryQuillen.cofibrations_eq, SSet.rlp_monomorphisms]
  exact M.retraction_mem_I_rlp

private theorem minimalSubfibration_inclusion_weak
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (M : MinimalFibration.MinimalSubfibration p) : WeakEquivalence M.carrier.ι := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  change realizationWeakEquivalences M.carrier.ι
  have hr : realizationWeakEquivalences M.sdr.r :=
    modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences M.sdr.r M.retraction_mem_I_rlp
  apply realizationWeakEquivalences.of_postcomp _ _ hr
  rw [M.sdr.retract]
  exact realizationWeakEquivalences.id_mem _

private abbrev minimalSpanLeg
    {E₀ E₁ B₀ B₁ : SSet.{u}} {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁}
    (M₀ : MinimalFibration.MinimalSubfibration p₀)
    (M₁ : MinimalFibration.MinimalSubfibration p₁) (f : E₀ ⟶ E₁) :
    (M₀.carrier : SSet.{u}) ⟶ (M₁.carrier : SSet.{u}) :=
  M₀.carrier.ι ≫ f ≫ M₁.sdr.r

private theorem minimalSpanLeg_isPullback_of_weakComparison
    {E₀ E₁ B₀ B₁ : SSet.{u}} (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁)
    [Fibration p₀] [Fibration p₁] (f : E₀ ⟶ E₁) (h : B₀ ⟶ B₁)
    (comm : f ≫ p₁ = p₀ ≫ h)
    (hw : WeakEquivalence (pullback.lift f p₀ comm))
    (M₀ : MinimalFibration.MinimalSubfibration p₀)
    (M₁ : MinimalFibration.MinimalSubfibration p₁) :
    IsPullback (minimalSpanLeg M₀ M₁ f) (M₀.carrier.ι ≫ p₀)
      (M₁.carrier.ι ≫ p₁) h := by
  let q₀ := M₀.carrier.ι ≫ p₀
  let q₁ := M₁.carrier.ι ≫ p₁
  have hr : M₁.sdr.r ≫ q₁ = p₁ := M₁.fiberwiseHomotopy.fac₁
  let β : pullback p₁ h ⟶ pullback q₁ h :=
    pullback.lift (pullback.fst p₁ h ≫ M₁.sdr.r) (pullback.snd p₁ h) (by
      rw [Category.assoc, hr]
      exact pullback.condition)
  have hβfst : β ≫ pullback.fst q₁ h = pullback.fst p₁ h ≫ M₁.sdr.r :=
    pullback.lift_fst _ _ _
  have hβsnd : β ≫ pullback.snd q₁ h = pullback.snd p₁ h := pullback.lift_snd _ _ _
  have houter : IsPullback (pullback.fst p₁ h) (β ≫ pullback.snd q₁ h)
      (M₁.sdr.r ≫ q₁) h := by
    rw [hβsnd, hr]
    exact IsPullback.of_hasPullback p₁ h
  have hβ : IsPullback (pullback.fst p₁ h) β M₁.sdr.r (pullback.fst q₁ h) :=
    houter.of_bot hβfst.symm (IsPullback.of_hasPullback q₁ h)
  have hβtriv : trivialFibrations SSet.{u} β :=
    MorphismProperty.of_isPullback hβ (minimalSubfibration_retraction_trivialFibration p₁ M₁)
  let _ : WeakEquivalence β := (mem_trivialFibrations_iff _).mp hβtriv |>.2
  let _ : WeakEquivalence M₀.carrier.ι := minimalSubfibration_inclusion_weak p₀ M₀
  let α := pullback.lift f p₀ comm
  let _ : WeakEquivalence α := hw
  have hleg : minimalSpanLeg M₀ M₁ f ≫ q₁ = q₀ ≫ h := by
    simp only [minimalSpanLeg, Category.assoc, hr, comm, q₀]
  let γ : (M₀.carrier : SSet.{u}) ⟶ pullback q₁ h :=
    pullback.lift (minimalSpanLeg M₀ M₁ f) q₀ hleg
  have hγ : γ = M₀.carrier.ι ≫ α ≫ β := by
    apply pullback.hom_ext
    · simp only [γ, Category.assoc, pullback.lift_fst, hβfst, α, minimalSpanLeg]
      rw [pullback.lift_fst_assoc]
    · simp only [γ, Category.assoc, pullback.lift_snd, hβsnd, α, q₀]
  let _ : WeakEquivalence γ := by rw [hγ]; infer_instance
  have hmin : MinimalFibration.IsMinimalFibration (pullback.snd q₁ h) :=
    MinimalFibration.isMinimalFibration_pullback_snd q₁ h M₁.isMinimalFibration
  let _ : IsIso γ := minimalFibration_isIso_of_weakEquivalence q₀ (pullback.snd q₁ h)
    M₀.isMinimalFibration hmin γ (pullback.lift_snd _ _ _)
  exact IsPullback.of_iso_pullback (CommSq.mk hleg) (asIso γ)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

private theorem exists_compatible_minimal_member_map
    {E₀ E₁ B₀ B₁ : SSet.{u}} (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁)
    [Fibration p₁] (f : E₀ ⟶ E₁) [Mono f] (h : B₀ ⟶ B₁)
    (comm : f ≫ p₁ = p₀ ≫ h)
    (M₀ : MinimalFibration.MinimalSubfibration p₀)
    (M₁ : MinimalFibration.MinimalSubfibration p₁) :
    ∃ r : E₁ ⟶ (M₁.carrier : SSet.{u}),
      r ≫ (M₁.carrier.ι ≫ p₁) = p₁ ∧
      f ≫ r = M₀.sdr.r ≫ minimalSpanLeg M₀ M₁ f ∧ WeakEquivalence r ∧
      Nonempty (FiberwiseHomotopy p₁ (M₁.carrier.ι ≫ p₁) M₁.sdr.r r) := by
  let q₁ := M₁.carrier.ι ≫ p₁
  let _ : Fibration q₁ := M₁.isMinimalFibration.1
  have hr : M₁.sdr.r ≫ q₁ = p₁ := by
    exact M₁.fiberwiseHomotopy.fac₁
  let H₀ := M₀.sdr.homotopy
  let hE := H₀.h ≫ f ≫ M₁.sdr.r
  let hB := fst E₁ (Δ[1] : SSet.{u}) ≫ p₁
  have hstart : f ≫ M₁.sdr.r = SSet.ι₀ ≫ hE := by
    simp only [hE, H₀, ← Category.assoc, M₀.sdr.homotopy.h₀, Category.id_comp]
  have hbaseStart : SSet.ι₀ ≫ hB = M₁.sdr.r ≫ q₁ := by
    simp only [hB, ι₀_fst_assoc, hr]
  have hEbase : hE ≫ q₁ = fst E₀ (Δ[1] : SSet.{u}) ≫ p₀ ≫ h := by
    calc
      hE ≫ q₁ = H₀.h ≫ f ≫ (M₁.sdr.r ≫ q₁) := by
        simp only [hE, Category.assoc]
      _ = H₀.h ≫ f ≫ p₁ := by rw [hr]
      _ = H₀.h ≫ p₀ ≫ h := by rw [comm]
      _ = fst E₀ (Δ[1] : SSet.{u}) ≫ p₀ ≫ h := by
        rw [← Category.assoc, M₀.over]
        simp only [Category.assoc]
  have hcompat : f ▷ (Δ[1] : SSet.{u}) ≫ hB = hE ≫ q₁ := by
    rw [hEbase]
    simp only [hB, whiskerRight_fst_assoc, comm]
  obtain ⟨Ψ, hΨ₀, hΨf, hΨp⟩ :=
    SSet.homotopy_extension_property₀ f q₁ hE M₁.sdr.r hstart hB hbaseStart hcompat
  let r := SSet.ι₁ ≫ Ψ
  let H : FiberwiseHomotopy p₁ q₁ M₁.sdr.r r :=
    { hom := Homotopy.mkOfH Ψ hΨ₀ rfl
      over := hΨp }
  have hleg : f ≫ r = M₀.sdr.r ≫ minimalSpanLeg M₀ M₁ f := by
    calc
      f ≫ r = SSet.ι₁ ≫ (f ▷ (Δ[1] : SSet.{u}) ≫ Ψ) := by
        simp only [r, ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ hE := by rw [hΨf]
      _ = M₀.sdr.r ≫ minimalSpanLeg M₀ M₁ f := by
        simp only [hE, H₀, minimalSpanLeg, ← Category.assoc, M₀.sdr.homotopy.h₁]
  have hw : WeakEquivalence r := by
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact (SSet.realizationWeakEquivalences_iff_of_homotopy H.hom).mp
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp
        (minimalSubfibration_retraction_weak p₁ M₁))
  exact ⟨r, H.fac₁, hleg, hw, ⟨H⟩⟩

private theorem exists_minimal_cartesian_span
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂)
    [Fibration p₀] [Fibration p₁] [Fibration p₂]
    (f₁ : E₀ ⟶ E₁) (f₂ : E₀ ⟶ E₂) [Mono f₁] [Mono f₂]
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂)
    (comm₁ : f₁ ≫ p₁ = p₀ ≫ h₁) (comm₂ : f₂ ≫ p₂ = p₀ ≫ h₂)
    (hw₁ : WeakEquivalence (pullback.lift f₁ p₀ comm₁))
    (hw₂ : WeakEquivalence (pullback.lift f₂ p₀ comm₂)) :
    ∃ (M₀ : MinimalFibration.MinimalSubfibration p₀)
      (M₁ : MinimalFibration.MinimalSubfibration p₁)
      (M₂ : MinimalFibration.MinimalSubfibration p₂)
      (r₁ : E₁ ⟶ (M₁.carrier : SSet.{u})) (r₂ : E₂ ⟶ (M₂.carrier : SSet.{u})),
      r₁ ≫ (M₁.carrier.ι ≫ p₁) = p₁ ∧ r₂ ≫ (M₂.carrier.ι ≫ p₂) = p₂ ∧
      WeakEquivalence r₁ ∧ WeakEquivalence r₂ ∧
      f₁ ≫ r₁ = M₀.sdr.r ≫ minimalSpanLeg M₀ M₁ f₁ ∧
      f₂ ≫ r₂ = M₀.sdr.r ≫ minimalSpanLeg M₀ M₂ f₂ ∧
      IsPullback (minimalSpanLeg M₀ M₁ f₁) (M₀.carrier.ι ≫ p₀) (M₁.carrier.ι ≫ p₁) h₁ ∧
      IsPullback (minimalSpanLeg M₀ M₂ f₂) (M₀.carrier.ι ≫ p₀) (M₂.carrier.ι ≫ p₂) h₂ := by
  obtain ⟨M₀⟩ := MinimalFibration.nonempty_minimalSubfibration p₀
  obtain ⟨M₁⟩ := MinimalFibration.nonempty_minimalSubfibration p₁
  obtain ⟨M₂⟩ := MinimalFibration.nonempty_minimalSubfibration p₂
  obtain ⟨r₁, hr₁, hf₁, hw₁', _⟩ :=
    exists_compatible_minimal_member_map p₀ p₁ f₁ h₁ comm₁ M₀ M₁
  obtain ⟨r₂, hr₂, hf₂, hw₂', _⟩ :=
    exists_compatible_minimal_member_map p₀ p₂ f₂ h₂ comm₂ M₀ M₂
  exact ⟨M₀, M₁, M₂, r₁, r₂, hr₁, hr₂, hw₁', hw₂', hf₁, hf₂,
    minimalSpanLeg_isPullback_of_weakComparison p₀ p₁ f₁ h₁ comm₁ hw₁ M₀ M₁,
    minimalSpanLeg_isPullback_of_weakComparison p₀ p₂ f₂ h₂ comm₂ hw₂ M₀ M₂⟩

private theorem exists_fill_of_cartesian_member
    {E₁ E B₁ B : SSet.{u}} (i : E₁ ⟶ E) (p₁ : E₁ ⟶ B₁) (p : E ⟶ B) (j : B₁ ⟶ B)
    [Fibration p₁] (member : IsPullback i p₁ p j) {n : ℕ} (k : Fin (n + 2))
    (a : (horn.{u} (n + 1) k : SSet.{u}) ⟶ E) (b : Δ[n + 1] ⟶ B)
    (sq : CommSq a (horn.{u} (n + 1) k).ι p b)
    (b₁ : Δ[n + 1] ⟶ B₁) (fac : b₁ ≫ j = b) :
    ∃ l : Δ[n + 1] ⟶ E, (horn.{u} (n + 1) k).ι ≫ l = a ∧ l ≫ p = b := by
  let a₁ := member.lift a ((horn.{u} (n + 1) k).ι ≫ b₁) (by
    rw [Category.assoc, fac]
    exact sq.w)
  have sq₁ : CommSq a₁ (horn.{u} (n + 1) k).ι p₁ b₁ :=
    ⟨member.lift_snd _ _ _⟩
  refine ⟨sq₁.lift ≫ i, ?_, ?_⟩
  · rw [← Category.assoc, sq₁.fac_left]
    exact member.lift_fst _ _ _
  · rw [Category.assoc, member.w, ← Category.assoc, sq₁.fac_right, fac]

private theorem fibration_of_cartesian_pushout
    {E₁ E₂ E B₀ B₁ B₂ B : SSet.{u}}
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂) (b₁ : B₁ ⟶ B) (b₂ : B₂ ⟶ B)
    (base : IsPushout h₁ h₂ b₁ b₂)
    (i₁ : E₁ ⟶ E) (i₂ : E₂ ⟶ E) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂) (p : E ⟶ B)
    [Fibration p₁] [Fibration p₂]
    (left : IsPullback i₁ p₁ p b₁) (right : IsPullback i₂ p₂ p b₂) : Fibration p := by
  rw [modelCategoryQuillen.fibration_iff]
  intro A D g hg
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨k⟩⟩ := hg
  constructor
  intro a b sq
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n + 1⦌)
  obtain ⟨x, hx⟩ | ⟨y, hy⟩ :=
    Types.eq_or_eq_of_isPushout (base.map ev) (yonedaEquiv b)
  · change b₁.app (op ⦋n + 1⦌) x = yonedaEquiv b at hx
    let c : Δ[n + 1] ⟶ B₁ := yonedaEquiv.symm x
    have hc : c ≫ b₁ = b := by
      apply yonedaEquiv.injective
      simpa only [c, yonedaEquiv_comp, Equiv.apply_symm_apply] using hx
    obtain ⟨l, hl, hr⟩ := exists_fill_of_cartesian_member i₁ p₁ p b₁ left k a b sq c hc
    exact CommSq.HasLift.mk' ⟨l, hl, hr⟩
  · change b₂.app (op ⦋n + 1⦌) y = yonedaEquiv b at hy
    let c : Δ[n + 1] ⟶ B₂ := yonedaEquiv.symm y
    have hc : c ≫ b₂ = b := by
      apply yonedaEquiv.injective
      simpa only [c, yonedaEquiv_comp, Equiv.apply_symm_apply] using hy
    obtain ⟨l, hl, hr⟩ := exists_fill_of_cartesian_member i₂ p₂ p b₂ right k a b sq c hc
    exact CommSq.HasLift.mk' ⟨l, hl, hr⟩

private def spanPushoutProjection
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    (sq₁ : CommSq f₁ p₀ p₁ h₁) (sq₂ : CommSq f₂ p₀ p₂ h₂) :
    pushout f₁ f₂ ⟶ pushout h₁ h₂ :=
  pushout.desc (p₁ ≫ pushout.inl h₁ h₂) (p₂ ≫ pushout.inr h₁ h₂) (by
    calc
      f₁ ≫ (p₁ ≫ pushout.inl h₁ h₂) = (f₁ ≫ p₁) ≫ pushout.inl h₁ h₂ :=
        (Category.assoc _ _ _).symm
      _ = (p₀ ≫ h₁) ≫ pushout.inl h₁ h₂ := by rw [sq₁.w]
      _ = p₀ ≫ (h₁ ≫ pushout.inl h₁ h₂) := Category.assoc _ _ _
      _ = p₀ ≫ (h₂ ≫ pushout.inr h₁ h₂) := by rw [pushout.condition]
      _ = (p₀ ≫ h₂) ≫ pushout.inr h₁ h₂ := (Category.assoc _ _ _).symm
      _ = (f₂ ≫ p₂) ≫ pushout.inr h₁ h₂ := by rw [sq₂.w]
      _ = f₂ ≫ (p₂ ≫ pushout.inr h₁ h₂) := Category.assoc _ _ _)

@[reassoc]
private theorem spanPushoutProjection_left
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    (sq₁ : CommSq f₁ p₀ p₁ h₁) (sq₂ : CommSq f₂ p₀ p₂ h₂) :
    pushout.inl f₁ f₂ ≫ spanPushoutProjection sq₁ sq₂ = p₁ ≫ pushout.inl h₁ h₂ := by
  rw [spanPushoutProjection, pushout.inl_desc]

@[reassoc]
private theorem spanPushoutProjection_right
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    (sq₁ : CommSq f₁ p₀ p₁ h₁) (sq₂ : CommSq f₂ p₀ p₂ h₂) :
    pushout.inr f₁ f₂ ≫ spanPushoutProjection sq₁ sq₂ = p₂ ≫ pushout.inr h₁ h₂ := by
  rw [spanPushoutProjection, pushout.inr_desc]

private theorem spanPushoutProjection_cartesian
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂} [Mono h₁]
    (sq₁ : IsPullback f₁ p₀ p₁ h₁) (sq₂ : IsPullback f₂ p₀ p₂ h₂) :
    IsPullback (pushout.inl f₁ f₂) p₁ (spanPushoutProjection sq₁.toCommSq sq₂.toCommSq)
        (pushout.inl h₁ h₂) ∧
      IsPullback (pushout.inr f₁ f₂) p₂ (spanPushoutProjection sq₁.toCommSq sq₂.toCommSq)
        (pushout.inr h₁ h₂) := by
  exact ((Adhesive.van_kampen (IsPushout.of_hasPushout h₁ h₂))
    f₁ f₂ (pushout.inl f₁ f₂) (pushout.inr f₁ f₂)
    p₀ p₁ p₂ (spanPushoutProjection sq₁.toCommSq sq₂.toCommSq) sq₁ sq₂
    (CommSq.mk (spanPushoutProjection_left sq₁.toCommSq sq₂.toCommSq))
    (CommSq.mk (spanPushoutProjection_right sq₁.toCommSq sq₂.toCommSq))
    (CommSq.mk (pushout.condition (f := f₁) (g := f₂)))).mp
      (IsPushout.of_hasPushout f₁ f₂)

private theorem spanPushoutProjection_fibration
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    [Mono h₁] [Fibration p₁] [Fibration p₂]
    (sq₁ : IsPullback f₁ p₀ p₁ h₁) (sq₂ : IsPullback f₂ p₀ p₂ h₂) :
    Fibration (spanPushoutProjection sq₁.toCommSq sq₂.toCommSq) := by
  obtain ⟨left, right⟩ := spanPushoutProjection_cartesian sq₁ sq₂
  exact fibration_of_cartesian_pushout h₁ h₂ (pushout.inl h₁ h₂) (pushout.inr h₁ h₂)
    (IsPushout.of_hasPushout h₁ h₂) (pushout.inl f₁ f₂) (pushout.inr f₁ f₂)
    p₁ p₂ (spanPushoutProjection sq₁.toCommSq sq₂.toCommSq) left right

private theorem exists_cartesian_pushout_fibration_model
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂)
    [Fibration p₀] [Fibration p₁] [Fibration p₂]
    (f₁ : E₀ ⟶ E₁) (f₂ : E₀ ⟶ E₂) [Mono f₁] [Mono f₂]
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂) [Mono h₁]
    (comm₁ : f₁ ≫ p₁ = p₀ ≫ h₁) (comm₂ : f₂ ≫ p₂ = p₀ ≫ h₂)
    (hw₁ : WeakEquivalence (pullback.lift f₁ p₀ comm₁))
    (hw₂ : WeakEquivalence (pullback.lift f₂ p₀ comm₂)) :
    ∃ (N : SSet.{u}) (q : N ⟶ pushout h₁ h₂) (u : pushout f₁ f₂ ⟶ N)
      (l₁ : E₁ ⟶ pullback q (pushout.inl h₁ h₂))
      (l₂ : E₂ ⟶ pullback q (pushout.inr h₁ h₂)),
      Fibration q ∧ WeakEquivalence u ∧
      u ≫ q = spanPushoutProjection (CommSq.mk comm₁) (CommSq.mk comm₂) ∧
      WeakEquivalence l₁ ∧ WeakEquivalence l₂ ∧
      l₁ ≫ pullback.fst q (pushout.inl h₁ h₂) = pushout.inl f₁ f₂ ≫ u ∧
      l₁ ≫ pullback.snd q (pushout.inl h₁ h₂) = p₁ ∧
      l₂ ≫ pullback.fst q (pushout.inr h₁ h₂) = pushout.inr f₁ f₂ ≫ u ∧
      l₂ ≫ pullback.snd q (pushout.inr h₁ h₂) = p₂ := by
  obtain ⟨M₀, M₁, M₂, r₁, r₂, hr₁, hr₂, wr₁, wr₂, hf₁, hf₂, sq₁, sq₂⟩ :=
    exists_minimal_cartesian_span p₀ p₁ p₂ f₁ f₂ h₁ h₂ comm₁ comm₂ hw₁ hw₂
  let m₁ := minimalSpanLeg M₀ M₁ f₁
  let m₂ := minimalSpanLeg M₀ M₂ f₂
  let q := spanPushoutProjection sq₁.toCommSq sq₂.toCommSq
  let u := pushout.map f₁ f₂ m₁ m₂ r₁ r₂ M₀.sdr.r hf₁ hf₂
  have hu₁ : pushout.inl f₁ f₂ ≫ u = r₁ ≫ pushout.inl m₁ m₂ := by
    dsimp only [u, pushout.map]
    rw [pushout.inl_desc]
  have hu₂ : pushout.inr f₁ f₂ ≫ u = r₂ ≫ pushout.inr m₁ m₂ := by
    dsimp only [u, pushout.map]
    rw [pushout.inr_desc]
  let _ : WeakEquivalence r₁ := wr₁
  let _ : WeakEquivalence r₂ := wr₂
  let _ : WeakEquivalence M₀.sdr.r := minimalSubfibration_retraction_weak p₀ M₀
  let _ : Cofibration f₁ := modelCategoryQuillen.cofibration_of_mono f₁
  let _ : Mono m₁ := sq₁.mono_fst_of_mono
  let _ : Cofibration m₁ := modelCategoryQuillen.cofibration_of_mono m₁
  have wu : WeakEquivalence u :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      (IsPushout.of_hasPushout f₁ f₂) (IsPushout.of_hasPushout m₁ m₂)
      hf₁ hf₂ hu₁ hu₂
  have hbase : u ≫ q = spanPushoutProjection (CommSq.mk comm₁) (CommSq.mk comm₂) := by
    apply (IsPushout.of_hasPushout f₁ f₂).hom_ext
    · rw [← Category.assoc, hu₁, Category.assoc]
      dsimp only [q]
      rw [spanPushoutProjection_left, ← Category.assoc, hr₁, spanPushoutProjection_left]
    · rw [← Category.assoc, hu₂, Category.assoc]
      dsimp only [q]
      rw [spanPushoutProjection_right, ← Category.assoc, hr₂, spanPushoutProjection_right]
  let _ : Fibration (M₁.carrier.ι ≫ p₁) := M₁.isMinimalFibration.1
  let _ : Fibration (M₂.carrier.ι ≫ p₂) := M₂.isMinimalFibration.1
  have fq : Fibration q := spanPushoutProjection_fibration sq₁ sq₂
  obtain ⟨left, right⟩ := spanPushoutProjection_cartesian sq₁ sq₂
  let e₁ := left.isoPullback
  let e₂ := right.isoPullback
  let l₁ := r₁ ≫ e₁.hom
  let l₂ := r₂ ≫ e₂.hom
  refine ⟨pushout m₁ m₂, q, u, l₁, l₂, fq, wu, hbase, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · dsimp only [l₁, e₁]
    rw [Category.assoc, left.isoPullback_hom_fst]
    exact hu₁.symm
  · dsimp only [l₁, e₁]
    rw [Category.assoc, left.isoPullback_hom_snd]
    exact hr₁
  · dsimp only [l₂, e₂]
    rw [Category.assoc, right.isoPullback_hom_fst]
    exact hu₂.symm
  · dsimp only [l₂, e₂]
    rw [Category.assoc, right.isoPullback_hom_snd]
    exact hr₂

private theorem exists_fibration_span
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂)
    (f₁ : E₀ ⟶ E₁) (f₂ : E₀ ⟶ E₂) [Mono f₁] [Mono f₂]
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂)
    (comm₁ : f₁ ≫ p₁ = p₀ ≫ h₁) (comm₂ : f₂ ≫ p₂ = p₀ ≫ h₂) :
    ∃ (F₀ F₁ F₂ : SSet.{u}) (q₀ : F₀ ⟶ B₀) (q₁ : F₁ ⟶ B₁) (q₂ : F₂ ⟶ B₂)
      (r₀ : E₀ ⟶ F₀) (r₁ : E₁ ⟶ F₁) (r₂ : E₂ ⟶ F₂)
      (g₁ : F₀ ⟶ F₁) (g₂ : F₀ ⟶ F₂),
      Fibration q₀ ∧ Fibration q₁ ∧ Fibration q₂ ∧
      WeakEquivalence r₀ ∧ WeakEquivalence r₁ ∧ WeakEquivalence r₂ ∧
      Mono g₁ ∧ Mono g₂ ∧
      r₀ ≫ q₀ = p₀ ∧ r₁ ≫ q₁ = p₁ ∧ r₂ ≫ q₂ = p₂ ∧
      f₁ ≫ r₁ = r₀ ≫ g₁ ∧ f₂ ≫ r₂ = r₀ ≫ g₂ ∧
      g₁ ≫ q₁ = q₀ ≫ h₁ ∧ g₂ ≫ q₂ = q₀ ≫ h₂ := by
  let d := MorphismProperty.factorizationData (trivialCofibrations SSet.{u})
    (fibrations SSet.{u}) p₀
  obtain ⟨hc₀, hw₀⟩ := (mem_trivialCofibrations_iff d.i).mp d.hi
  let _ : Fibration d.p := (HomotopicalAlgebra.fibration_iff _).mpr d.hp
  obtain ⟨F₁, r₁, g₁, q₁, hr₁, hg₁, hq₁, fac₁, facg₁, nat₁⟩ :=
    exists_fibration_span_leg f₁ d.i d.hi p₁ (d.p ≫ h₁) (by
      rw [← Category.assoc, d.fac]
      exact comm₁)
  obtain ⟨F₂, r₂, g₂, q₂, hr₂, hg₂, hq₂, fac₂, facg₂, nat₂⟩ :=
    exists_fibration_span_leg f₂ d.i d.hi p₂ (d.p ≫ h₂) (by
      rw [← Category.assoc, d.fac]
      exact comm₂)
  have hm₁ : Mono g₁ := (modelCategoryQuillen.cofibration_iff g₁).mp hg₁
  have hm₂ : Mono g₂ := (modelCategoryQuillen.cofibration_iff g₂).mp hg₂
  exact ⟨d.Z, F₁, F₂, d.p, q₁, q₂, d.i, r₁, r₂, g₁, g₂,
    inferInstance, hq₁, hq₂, hw₀,
    ((mem_trivialCofibrations_iff r₁).mp hr₁).2,
    ((mem_trivialCofibrations_iff r₂).mp hr₂).2,
    hm₁, hm₂, d.fac, fac₁, fac₂, nat₁, nat₂, facg₁, facg₂⟩

end SSet

namespace TopCat

theorem homotopyPullbackComparison_eq_lift
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} (sq : CommSq s q p h) :
    homotopyPullbackComparison sq = pullback.lift s q sq.w ≫
      homotopyPullbackComparison (IsPullback.of_hasPullback p h).toCommSq := by
  apply homotopyPullback_hom_ext
  · simp only [Category.assoc, homotopyPullbackComparison_left, pullback.lift_fst]
  · simp only [Category.assoc, homotopyPullbackComparison_right, pullback.lift_snd]
  · simp only [Category.assoc, homotopyPullbackComparison_path, pullback.lift_fst_assoc]

private theorem weak_pullback_lift_of_comparison
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} [Fibration p] (sq : CommSq s q p h)
    (hw : weakHomotopyEquivalences (homotopyPullbackComparison sq)) :
    weakHomotopyEquivalences (pullback.lift s q sq.w) := by
  rw [homotopyPullbackComparison_eq_lift] at hw
  exact weakHomotopyEquivalences.of_postcomp _ _
    (homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback p h)) hw

theorem homotopyPullbackComparison_weak_iff_of_map
    {A E W B A' E' W' B' : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    {s' : A' ⟶ E'} {q' : A' ⟶ W'} {p' : E' ⟶ B'} {h' : W' ⟶ B'}
    (sq : CommSq s q p h) (sq' : CommSq s' q' p' h')
    (a : A ⟶ A') (e : E ⟶ E') (w : W ⟶ W') (b : B ⟶ B')
    (hs : s ≫ e = a ≫ s') (hq : q ≫ w = a ≫ q')
    (hp : p ≫ b = e ≫ p') (hh : h ≫ b = w ≫ h')
    (wa : weakHomotopyEquivalences a) (we : weakHomotopyEquivalences e)
    (ww : weakHomotopyEquivalences w) (wb : weakHomotopyEquivalences b) :
    weakHomotopyEquivalences (homotopyPullbackComparison sq) ↔
      weakHomotopyEquivalences (homotopyPullbackComparison sq') := by
  have wm := homotopyPullbackMap_mem_weakHomotopyEquivalences e w b hp hh we ww wb
  have nat := homotopyPullbackComparison_naturality sq sq' a e w b hs hq hp hh
  constructor
  · intro hc
    apply weakHomotopyEquivalences.of_precomp _ _ wa
    rw [← nat]
    exact weakHomotopyEquivalences.comp_mem _ _ hc wm
  · intro hc
    apply weakHomotopyEquivalences.of_postcomp _ _ wm
    rw [nat]
    exact weakHomotopyEquivalences.comp_mem _ _ wa hc

private theorem pullbackMap_weak_of_fibrations_and_weak_base
    {M N W B₀ B : TopCat.{u}} (p : M ⟶ B₀) (q : N ⟶ B)
    [Fibration p] [Fibration q] (f : M ⟶ N) (b : B₀ ⟶ B)
    (hf : f ≫ q = p ≫ b) (h : W ⟶ B₀)
    (wf : weakHomotopyEquivalences f) (wb : weakHomotopyEquivalences b) :
    weakHomotopyEquivalences (pullback.lift
      (pullback.fst p h ≫ f) (pullback.snd p h) (by
        rw [Category.assoc, hf, ← Category.assoc, pullback.condition, Category.assoc])) := by
  let φ := pullback.lift (pullback.fst p h ≫ f) (pullback.snd p h) (by
    rw [Category.assoc, hf, ← Category.assoc, pullback.condition, Category.assoc])
  have nat := homotopyPullbackComparison_naturality
    (IsPullback.of_hasPullback p h).toCommSq
    (IsPullback.of_hasPullback q (h ≫ b)).toCommSq
    φ f (𝟙 W) b
    (by dsimp only [φ]; rw [pullback.lift_fst])
    (by dsimp only [φ]; rw [pullback.lift_snd, Category.comp_id])
    hf.symm (by rw [Category.id_comp])
  have wm := homotopyPullbackMap_mem_weakHomotopyEquivalences (g := h) f (𝟙 W) b hf.symm
    (by rw [Category.id_comp]) wf (weakHomotopyEquivalences.of_isIso _) wb
  apply weakHomotopyEquivalences.of_postcomp _ _
    (homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback q (h ≫ b)))
  rw [← nat]
  exact weakHomotopyEquivalences.comp_mem _ _
    (homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback p h)) wm

private theorem exists_fibration_extension
    {A E M B₀ B : TopCat.{u}}
    (a : A ⟶ E) [Cofibration a] [WeakEquivalence a]
    (u : A ⟶ M) [WeakEquivalence u] (p₀ : M ⟶ B₀) (b : B₀ ⟶ B) (p : E ⟶ B)
    (comm : a ≫ p = u ≫ p₀ ≫ b) :
    ∃ (N : TopCat.{u}) (q : N ⟶ B) (j : M ⟶ N) (v : E ⟶ N),
      Fibration q ∧ WeakEquivalence j ∧ WeakEquivalence v ∧
      j ≫ q = p₀ ≫ b ∧ a ≫ v = u ≫ j ∧ v ≫ q = p := by
  let d := MorphismProperty.factorizationData (trivialCofibrations TopCat.{u})
    (fibrations TopCat.{u}) (p₀ ≫ b)
  obtain ⟨hc, hw⟩ := (mem_trivialCofibrations_iff d.i).mp d.hi
  let _ : WeakEquivalence d.i := hw
  let _ : Fibration d.p := (fibration_iff _).mpr d.hp
  let sq : CommSq (u ≫ d.i) a d.p p := ⟨by
    rw [Category.assoc, d.fac]
    exact comm.symm⟩
  let v := sq.lift
  have wv : WeakEquivalence v :=
    weakEquivalence_of_precomp_of_fac sq.fac_left
  exact ⟨d.Z, d.p, d.i, v, inferInstance, hw, wv, d.fac, sq.fac_left, sq.fac_right⟩

private theorem front_comparison_weak_of_model_member
    {A E M N W B₀ B : TopCat.{u}}
    {s : A ⟶ E} {p : E ⟶ B} {a : A ⟶ W}
    (p₀ : M ⟶ B₀) (q : N ⟶ B) [Fibration p₀] [Fibration q]
    (j : M ⟶ N) (b : B₀ ⟶ B) (h : W ⟶ B₀)
    (hj : j ≫ q = p₀ ≫ b) (wj : weakHomotopyEquivalences j)
    (wb : weakHomotopyEquivalences b)
    (v : E ⟶ N) (hv : v ≫ q = p) (wv : weakHomotopyEquivalences v)
    (sq : CommSq s a p (h ≫ b))
    (k : A ⟶ pullback p₀ h) (wk : weakHomotopyEquivalences k)
    (hkE : k ≫ pullback.fst p₀ h ≫ j = s ≫ v)
    (hkB : k ≫ pullback.snd p₀ h = a) :
    weakHomotopyEquivalences (homotopyPullbackComparison sq) := by
  let sq' : CommSq (s ≫ v) a q (h ≫ b) := ⟨by
    rw [Category.assoc, hv]
    exact sq.w⟩
  let φ := pullback.lift (pullback.fst p₀ h ≫ j) (pullback.snd p₀ h) (by
    rw [Category.assoc, hj, ← Category.assoc, pullback.condition, Category.assoc])
  have wφ : weakHomotopyEquivalences φ :=
    pullbackMap_weak_of_fibrations_and_weak_base p₀ q j b hj h wj wb
  have hβ : k ≫ φ = pullback.lift (s ≫ v) a sq'.w := by
    apply pullback.hom_ext
    · dsimp only [φ]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hkE
    · dsimp only [φ]
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact hkB
  have wc : weakHomotopyEquivalences (homotopyPullbackComparison sq') := by
    rw [homotopyPullbackComparison_eq_lift, ← hβ]
    exact weakHomotopyEquivalences.comp_mem _ _
      (weakHomotopyEquivalences.comp_mem _ _ wk wφ)
      (homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback q (h ≫ b)))
  exact (homotopyPullbackComparison_weak_iff_of_map sq sq' (𝟙 A) v (𝟙 W) (𝟙 B)
    (by simp only [Category.id_comp])
    (by simp only [Category.comp_id, Category.id_comp])
    (by simp only [Category.comp_id, hv])
    (by simp only [Category.comp_id, Category.id_comp])
    (weakHomotopyEquivalences.of_isIso _) wv
    (weakHomotopyEquivalences.of_isIso _) (weakHomotopyEquivalences.of_isIso _)).mpr wc

end TopCat

namespace SSet

open scoped SSet.modelCategoryQuillen

private theorem toTop_map_weak {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    TopCat.weakHomotopyEquivalences (SSet.toTop.map f) := by
  have hw : realizationWeakEquivalences f :=
    (weakEquivalence_iff f).mp inferInstance
  exact hw

private theorem weak_pullback_lift_of_realized_comparison
    {A E W B : SSet.{u}} {s : A ⟶ E} {q : A ⟶ W}
    {p : E ⟶ B} {h : W ⟶ B} [Fibration p] [Mono h]
    (sq : CommSq s q p h)
    (hw : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq sq))) :
    WeakEquivalence (pullback.lift s q sq.w) := by
  have realPB := ((IsPullback.of_hasPullback p h).flip.map_toTop_of_mono).flip
  let e := realPB.isoPullback
  have he : SSet.toTop.map (pullback.lift s q sq.w) ≫ e.hom =
      pullback.lift (SSet.toTop.map s) (SSet.toTop.map q)
        (SSet.toTop.map_commSq sq).w := by
    apply pullback.hom_ext
    · dsimp only [e]
      rw [Category.assoc, realPB.isoPullback_hom_fst, ← SSet.toTop.map_comp,
        pullback.lift_fst]
      exact (pullback.lift_fst _ _ _).symm
    · dsimp only [e]
      rw [Category.assoc, realPB.isoPullback_hom_snd, ← SSet.toTop.map_comp,
        pullback.lift_snd]
      exact (pullback.lift_snd _ _ _).symm
  have wl := TopCat.weak_pullback_lift_of_comparison (SSet.toTop.map_commSq sq) hw
  have wr : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (pullback.lift s q sq.w)) := by
    apply TopCat.weakHomotopyEquivalences.of_postcomp _ _
      (TopCat.weakHomotopyEquivalences.of_isIso e.hom)
    rw [he]
    exact wl
  exact (weakEquivalence_iff _).mpr wr

private theorem realized_back_comparison_weak_of_spanMap
    {E₀ E₁ F₀ F₁ B₀ B₁ : SSet.{u}}
    {f : E₀ ⟶ E₁} {g : F₀ ⟶ F₁} {h : B₀ ⟶ B₁}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {q₀ : F₀ ⟶ B₀} {q₁ : F₁ ⟶ B₁}
    (sq : CommSq f p₀ p₁ h) (sq' : CommSq g q₀ q₁ h)
    (r₀ : E₀ ⟶ F₀) (r₁ : E₁ ⟶ F₁) [WeakEquivalence r₀] [WeakEquivalence r₁]
    (nat : f ≫ r₁ = r₀ ≫ g) (fac₀ : r₀ ≫ q₀ = p₀) (fac₁ : r₁ ≫ q₁ = p₁)
    (hw : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq sq))) :
    TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq sq')) := by
  apply (TopCat.homotopyPullbackComparison_weak_iff_of_map
    (SSet.toTop.map_commSq sq) (SSet.toTop.map_commSq sq')
    (SSet.toTop.map r₀) (SSet.toTop.map r₁) (𝟙 _) (𝟙 _)
    (by simpa only [← SSet.toTop.map_comp] using congrArg SSet.toTop.map nat)
    (by simp only [Category.comp_id, ← SSet.toTop.map_comp, fac₀])
    (by simp only [Category.comp_id, ← SSet.toTop.map_comp, fac₁])
    (by simp only [Category.comp_id, Category.id_comp])
    (toTop_map_weak r₀) (toTop_map_weak r₁)
    (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.of_isIso _)).mp
  exact hw

private theorem exists_cartesian_pushout_model_of_realized_comparisons
    {E₀ E₁ E₂ B₀ B₁ B₂ : SSet.{u}}
    (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂)
    (f₁ : E₀ ⟶ E₁) (f₂ : E₀ ⟶ E₂) [Mono f₁] [Mono f₂]
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂) [Mono h₁] [Mono h₂]
    (comm₁ : f₁ ≫ p₁ = p₀ ≫ h₁) (comm₂ : f₂ ≫ p₂ = p₀ ≫ h₂)
    (hw₁ : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq (CommSq.mk comm₁))))
    (hw₂ : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq (CommSq.mk comm₂)))) :
    ∃ (N : SSet.{u}) (q : N ⟶ pushout h₁ h₂) (u : pushout f₁ f₂ ⟶ N)
      (l₁ : E₁ ⟶ pullback q (pushout.inl h₁ h₂))
      (l₂ : E₂ ⟶ pullback q (pushout.inr h₁ h₂)),
      Fibration q ∧ WeakEquivalence u ∧
      u ≫ q = spanPushoutProjection (CommSq.mk comm₁) (CommSq.mk comm₂) ∧
      WeakEquivalence l₁ ∧ WeakEquivalence l₂ ∧
      l₁ ≫ pullback.fst q (pushout.inl h₁ h₂) = pushout.inl f₁ f₂ ≫ u ∧
      l₁ ≫ pullback.snd q (pushout.inl h₁ h₂) = p₁ ∧
      l₂ ≫ pullback.fst q (pushout.inr h₁ h₂) = pushout.inr f₁ f₂ ≫ u ∧
      l₂ ≫ pullback.snd q (pushout.inr h₁ h₂) = p₂ := by
  obtain ⟨F₀, F₁, F₂, q₀, q₁, q₂, r₀, r₁, r₂, g₁, g₂,
    fq₀, fq₁, fq₂, wr₀, wr₁, wr₂, mg₁, mg₂, fac₀, fac₁, fac₂,
    nat₁, nat₂, commg₁, commg₂⟩ :=
    exists_fibration_span p₀ p₁ p₂ f₁ f₂ h₁ h₂ comm₁ comm₂
  let _ : Fibration q₀ := fq₀
  let _ : Fibration q₁ := fq₁
  let _ : Fibration q₂ := fq₂
  let _ : WeakEquivalence r₀ := wr₀
  let _ : WeakEquivalence r₁ := wr₁
  let _ : WeakEquivalence r₂ := wr₂
  let _ : Mono g₁ := mg₁
  let _ : Mono g₂ := mg₂
  have wg₁ := weak_pullback_lift_of_realized_comparison (CommSq.mk commg₁)
    (realized_back_comparison_weak_of_spanMap (CommSq.mk comm₁) (CommSq.mk commg₁)
      r₀ r₁ nat₁ fac₀ fac₁ hw₁)
  have wg₂ := weak_pullback_lift_of_realized_comparison (CommSq.mk commg₂)
    (realized_back_comparison_weak_of_spanMap (CommSq.mk comm₂) (CommSq.mk commg₂)
      r₀ r₂ nat₂ fac₀ fac₂ hw₂)
  obtain ⟨N, q, v, k₁, k₂, fq, wv, facv, wk₁, wk₂,
    hk₁E, hk₁B, hk₂E, hk₂B⟩ :=
    exists_cartesian_pushout_fibration_model q₀ q₁ q₂ g₁ g₂ h₁ h₂
      commg₁ commg₂ wg₁ wg₂
  let t := pushout.map f₁ f₂ g₁ g₂ r₁ r₂ r₀ nat₁ nat₂
  have ht₁ : pushout.inl f₁ f₂ ≫ t = r₁ ≫ pushout.inl g₁ g₂ := by
    dsimp only [t, pushout.map]
    rw [pushout.inl_desc]
  have ht₂ : pushout.inr f₁ f₂ ≫ t = r₂ ≫ pushout.inr g₁ g₂ := by
    dsimp only [t, pushout.map]
    rw [pushout.inr_desc]
  let _ : Cofibration f₁ := modelCategoryQuillen.cofibration_of_mono f₁
  let _ : Cofibration g₁ := modelCategoryQuillen.cofibration_of_mono g₁
  have wt : WeakEquivalence t :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      (IsPushout.of_hasPushout f₁ f₂) (IsPushout.of_hasPushout g₁ g₂)
      nat₁ nat₂ ht₁ ht₂
  let _ : WeakEquivalence t := wt
  let _ : WeakEquivalence v := wv
  let _ : WeakEquivalence k₁ := wk₁
  let _ : WeakEquivalence k₂ := wk₂
  refine ⟨N, q, t ≫ v, r₁ ≫ k₁, r₂ ≫ k₂, fq, inferInstance, ?_,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · apply (IsPushout.of_hasPushout f₁ f₂).hom_ext
    · rw [← Category.assoc, ← Category.assoc, ht₁, Category.assoc, Category.assoc,
        facv, spanPushoutProjection_left, ← Category.assoc, fac₁,
        spanPushoutProjection_left]
    · rw [← Category.assoc, ← Category.assoc, ht₂, Category.assoc, Category.assoc,
        facv, spanPushoutProjection_right, ← Category.assoc, fac₂,
        spanPushoutProjection_right]
  · rw [Category.assoc, hk₁E, ← Category.assoc, ← ht₁, Category.assoc]
  · rw [Category.assoc, hk₁B, fac₁]
  · rw [Category.assoc, hk₂E, ← Category.assoc, ← ht₂, Category.assoc]
  · rw [Category.assoc, hk₂B, fac₂]

private theorem realized_span_front_left_square
    {E₀ E₁ E₂ E B₀ B₁ B₂ : SSet.{u}} {B : TopCat.{u}}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    (sq₁ : CommSq f₁ p₀ p₁ h₁) (sq₂ : CommSq f₂ p₀ p₂ h₂)
    (a : pushout f₁ f₂ ⟶ E) (b : SSet.toTop.obj (pushout h₁ h₂) ⟶ B)
    (p : SSet.toTop.obj E ⟶ B)
    (compat : SSet.toTop.map a ≫ p = SSet.toTop.map (spanPushoutProjection sq₁ sq₂) ≫ b) :
    CommSq (SSet.toTop.map (pushout.inl f₁ f₂ ≫ a)) (SSet.toTop.map p₁)
      p (SSet.toTop.map (pushout.inl h₁ h₂) ≫ b) := ⟨by
    rw [SSet.toTop.map_comp, Category.assoc, compat, ← Category.assoc,
      ← SSet.toTop.map_comp, spanPushoutProjection_left,
      SSet.toTop.map_comp, Category.assoc]⟩

private theorem realized_span_front_right_square
    {E₀ E₁ E₂ E B₀ B₁ B₂ : SSet.{u}} {B : TopCat.{u}}
    {p₀ : E₀ ⟶ B₀} {p₁ : E₁ ⟶ B₁} {p₂ : E₂ ⟶ B₂}
    {f₁ : E₀ ⟶ E₁} {f₂ : E₀ ⟶ E₂} {h₁ : B₀ ⟶ B₁} {h₂ : B₀ ⟶ B₂}
    (sq₁ : CommSq f₁ p₀ p₁ h₁) (sq₂ : CommSq f₂ p₀ p₂ h₂)
    (a : pushout f₁ f₂ ⟶ E) (b : SSet.toTop.obj (pushout h₁ h₂) ⟶ B)
    (p : SSet.toTop.obj E ⟶ B)
    (compat : SSet.toTop.map a ≫ p = SSet.toTop.map (spanPushoutProjection sq₁ sq₂) ≫ b) :
    CommSq (SSet.toTop.map (pushout.inr f₁ f₂ ≫ a)) (SSet.toTop.map p₂)
      p (SSet.toTop.map (pushout.inr h₁ h₂) ≫ b) := ⟨by
    rw [SSet.toTop.map_comp, Category.assoc, compat, ← Category.assoc,
      ← SSet.toTop.map_comp, spanPushoutProjection_right,
      SSet.toTop.map_comp, Category.assoc]⟩

private theorem realized_front_comparisons_weak
    {E₀ E₁ E₂ E B₀ B₁ B₂ : SSet.{u}} {B : TopCat.{u}}
    (p₀ : E₀ ⟶ B₀) (p₁ : E₁ ⟶ B₁) (p₂ : E₂ ⟶ B₂)
    (f₁ : E₀ ⟶ E₁) (f₂ : E₀ ⟶ E₂) [Mono f₁] [Mono f₂]
    (h₁ : B₀ ⟶ B₁) (h₂ : B₀ ⟶ B₂) [Mono h₁] [Mono h₂]
    (comm₁ : f₁ ≫ p₁ = p₀ ≫ h₁) (comm₂ : f₂ ≫ p₂ = p₀ ≫ h₂)
    (a : pushout f₁ f₂ ⟶ E) [Mono a] [WeakEquivalence a]
    (b : SSet.toTop.obj (pushout h₁ h₂) ⟶ B) (wb : TopCat.weakHomotopyEquivalences b)
    (p : SSet.toTop.obj E ⟶ B)
    (compat : SSet.toTop.map a ≫ p =
      SSet.toTop.map (spanPushoutProjection (CommSq.mk comm₁) (CommSq.mk comm₂)) ≫ b)
    (front₁ : CommSq (SSet.toTop.map (pushout.inl f₁ f₂ ≫ a)) (SSet.toTop.map p₁)
      p (SSet.toTop.map (pushout.inl h₁ h₂) ≫ b))
    (front₂ : CommSq (SSet.toTop.map (pushout.inr f₁ f₂ ≫ a)) (SSet.toTop.map p₂)
      p (SSet.toTop.map (pushout.inr h₁ h₂) ≫ b))
    (hw₁ : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq (CommSq.mk comm₁))))
    (hw₂ : TopCat.weakHomotopyEquivalences
      (TopCat.homotopyPullbackComparison (SSet.toTop.map_commSq (CommSq.mk comm₂)))) :
    TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison front₁) ∧
      TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison front₂) := by
  obtain ⟨M, q₀, u, l₁, l₂, fq₀, wu, facu, wl₁, wl₂,
    hl₁E, hl₁B, hl₂E, hl₂B⟩ :=
    exists_cartesian_pushout_model_of_realized_comparisons p₀ p₁ p₂ f₁ f₂ h₁ h₂
      comm₁ comm₂ hw₁ hw₂
  let _ : Fibration q₀ := fq₀
  let _ : WeakEquivalence u := wu
  let _ : WeakEquivalence l₁ := wl₁
  let _ : WeakEquivalence l₂ := wl₂
  let _ : Cofibration a := modelCategoryQuillen.cofibration_of_mono a
  let _ : Cofibration (SSet.toTop.map a) := (cofibration_iff _).mpr
    (CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrations
      (adj := sSetTopAdj) a ((cofibration_iff a).mp inferInstance))
  let _ : WeakEquivalence (SSet.toTop.map a) :=
    (weakEquivalence_iff _).mpr (toTop_map_weak a)
  let _ : WeakEquivalence (SSet.toTop.map u) :=
    (weakEquivalence_iff _).mpr (toTop_map_weak u)
  obtain ⟨N, q, j, v, fq, wj, wv, hj, hav, hv⟩ :=
    TopCat.exists_fibration_extension (SSet.toTop.map a) (SSet.toTop.map u)
      (SSet.toTop.map q₀) b p (by
        rw [← Category.assoc, ← SSet.toTop.map_comp, facu]
        exact compat)
  let _ : Fibration q := fq
  let _ : Cofibration h₁ := modelCategoryQuillen.cofibration_of_mono h₁
  let _ : Cofibration h₂ := modelCategoryQuillen.cofibration_of_mono h₂
  let _ : Mono (pushout.inl h₁ h₂) :=
    (modelCategoryQuillen.cofibration_iff _).mp inferInstance
  let _ : Mono (pushout.inr h₁ h₂) :=
    (modelCategoryQuillen.cofibration_iff _).mp inferInstance
  have realPB₁ :=
    ((IsPullback.of_hasPullback q₀ (pushout.inl h₁ h₂)).flip.map_toTop_of_mono).flip
  have realPB₂ :=
    ((IsPullback.of_hasPullback q₀ (pushout.inr h₁ h₂)).flip.map_toTop_of_mono).flip
  let e₁ := realPB₁.isoPullback
  let e₂ := realPB₂.isoPullback
  let k₁ := SSet.toTop.map l₁ ≫ e₁.hom
  let k₂ := SSet.toTop.map l₂ ≫ e₂.hom
  have wk₁ : TopCat.weakHomotopyEquivalences k₁ :=
    TopCat.weakHomotopyEquivalences.comp_mem _ _ (toTop_map_weak l₁)
      (TopCat.weakHomotopyEquivalences.of_isIso e₁.hom)
  have wk₂ : TopCat.weakHomotopyEquivalences k₂ :=
    TopCat.weakHomotopyEquivalences.comp_mem _ _ (toTop_map_weak l₂)
      (TopCat.weakHomotopyEquivalences.of_isIso e₂.hom)
  have hk₁E : k₁ ≫ pullback.fst (SSet.toTop.map q₀)
        (SSet.toTop.map (pushout.inl h₁ h₂)) ≫ j =
      SSet.toTop.map (pushout.inl f₁ f₂ ≫ a) ≫ v := by
    dsimp only [k₁, e₁]
    rw [Category.assoc, realPB₁.isoPullback_hom_fst_assoc,
      ← Category.assoc, ← SSet.toTop.map_comp, hl₁E, SSet.toTop.map_comp,
      Category.assoc, ← hav, ← Category.assoc, ← SSet.toTop.map_comp]
  have hk₁B : k₁ ≫ pullback.snd (SSet.toTop.map q₀)
      (SSet.toTop.map (pushout.inl h₁ h₂)) = SSet.toTop.map p₁ := by
    dsimp only [k₁, e₁]
    rw [Category.assoc, realPB₁.isoPullback_hom_snd, ← SSet.toTop.map_comp, hl₁B]
  have hk₂E : k₂ ≫ pullback.fst (SSet.toTop.map q₀)
        (SSet.toTop.map (pushout.inr h₁ h₂)) ≫ j =
      SSet.toTop.map (pushout.inr f₁ f₂ ≫ a) ≫ v := by
    dsimp only [k₂, e₂]
    rw [Category.assoc, realPB₂.isoPullback_hom_fst_assoc,
      ← Category.assoc, ← SSet.toTop.map_comp, hl₂E, SSet.toTop.map_comp,
      Category.assoc, ← hav, ← Category.assoc, ← SSet.toTop.map_comp]
  have hk₂B : k₂ ≫ pullback.snd (SSet.toTop.map q₀)
      (SSet.toTop.map (pushout.inr h₁ h₂)) = SSet.toTop.map p₂ := by
    dsimp only [k₂, e₂]
    rw [Category.assoc, realPB₂.isoPullback_hom_snd, ← SSet.toTop.map_comp, hl₂B]
  exact ⟨TopCat.front_comparison_weak_of_model_member (SSet.toTop.map q₀) q j b
    (SSet.toTop.map (pushout.inl h₁ h₂)) hj ((weakEquivalence_iff j).mp wj) wb
    v hv ((weakEquivalence_iff v).mp wv) front₁ k₁ wk₁ hk₁E hk₁B,
    TopCat.front_comparison_weak_of_model_member (SSet.toTop.map q₀) q j b
    (SSet.toTop.map (pushout.inr h₁ h₂)) hj ((weakEquivalence_iff j).mp wj) wb
    v hv ((weakEquivalence_iff v).mp wv) front₂ k₂ wk₂ hk₂E hk₂B⟩

end SSet

namespace TopCat

open scoped SSet.modelCategoryQuillen

private def subordinateRestrictionProjection {E B : TopCat.{u}}
    (p : E ⟶ B) (W : Set B) :
    (AlgebraicTopology.subordinateSet (p ⁻¹' W) : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet W : SSet.{u}) :=
  SSet.Subcomplex.lift ((AlgebraicTopology.subordinateSet (p ⁻¹' W)).ι ≫
    TopCat.toSSet.map p) (by
      rw [← SSet.Subcomplex.image_eq_range]
      exact AlgebraicTopology.subordinateSet_image_le p (fun _ hx => hx))

@[reassoc]
private theorem subordinateRestrictionProjection_ι {E B : TopCat.{u}}
    (p : E ⟶ B) (W : Set B) :
    subordinateRestrictionProjection p W ≫ (AlgebraicTopology.subordinateSet W).ι =
      (AlgebraicTopology.subordinateSet (p ⁻¹' W)).ι ≫ TopCat.toSSet.map p := by
  rw [subordinateRestrictionProjection, SSet.Subcomplex.lift_ι]

private theorem subordinateRestrictionProjection_evaluation {E B : TopCat.{u}}
    (p : E ⟶ B) (W : Set B) :
    SSet.toTop.map (subordinateRestrictionProjection p W) ≫
        realizedSubordinateSetEvaluation W =
      realizedSubordinateSetEvaluation (p ⁻¹' W) ≫ restrictionProjection p W := by
  apply (cancel_mono (AlgebraicTopology.subspaceIncl W)).mp
  rw [Category.assoc, realizedSubordinateSetEvaluation_inclusion,
    ← Category.assoc, ← SSet.toTop.map_comp, subordinateRestrictionProjection_ι,
    SSet.toTop.map_comp, Category.assoc]
  have hn : SSet.toTop.map (TopCat.toSSet.map p) ≫ sSetTopAdj.counit.app B =
      sSetTopAdj.counit.app E ≫ p := by
    simpa only [Functor.comp_map, Functor.id_map] using sSetTopAdj.counit.naturality p
  rw [hn, ← Category.assoc, ← realizedSubordinateSetEvaluation_inclusion,
    Category.assoc, (restrictionProjection_isPullback p W).w]
  rw [Category.assoc]

private theorem subordinateRestriction_nested_square {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    CommSq
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono (Set.preimage_mono hWU)))
      (subordinateRestrictionProjection p W) (subordinateRestrictionProjection p U)
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono hWU)) := ⟨by
    apply (cancel_mono (AlgebraicTopology.subordinateSet U).ι).mp
    simp only [Category.assoc, subordinateRestrictionProjection_ι,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι_assoc]⟩

private theorem subordinateRestriction_back_comparison_weak {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U)
    (hw : weakHomotopyEquivalences (homotopyPullbackComparison
      (restrictionProjection_nested_isPullback p hWU).toCommSq)) :
    weakHomotopyEquivalences (homotopyPullbackComparison
      (SSet.toTop.map_commSq (subordinateRestriction_nested_square p hWU))) := by
  exact (homotopyPullbackComparison_weak_iff_of_map
    (SSet.toTop.map_commSq (subordinateRestriction_nested_square p hWU))
    (restrictionProjection_nested_isPullback p hWU).toCommSq
    (realizedSubordinateSetEvaluation (p ⁻¹' W))
    (realizedSubordinateSetEvaluation (p ⁻¹' U))
    (realizedSubordinateSetEvaluation W) (realizedSubordinateSetEvaluation U)
    (by
      rw [restrictionTotalInclusion_eq_subspaceInclOfSubset]
      exact realizedSubordinateSetInclusion_evaluation
        (Set.preimage_mono hWU : p ⁻¹' W ⊆ p ⁻¹' U))
    (subordinateRestrictionProjection_evaluation p W)
    (subordinateRestrictionProjection_evaluation p U)
    (realizedSubordinateSetInclusion_evaluation hWU)
    (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
    (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
    (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
    (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)).mpr hw

private theorem subordinateCover_isPushout {X : TopCat.{u}} (U V : Set X) :
    IsPushout
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left))
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right))
      (SSet.Subcomplex.homOfLE (show AlgebraicTopology.subordinateSet U ≤
        AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V from le_sup_left))
      (SSet.Subcomplex.homOfLE (show AlgebraicTopology.subordinateSet V ≤
        AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V
        from le_sup_right)) := by
  let sq : SSet.Subcomplex.BicartSq (AlgebraicTopology.subordinateSet (U ∩ V))
      (AlgebraicTopology.subordinateSet U) (AlgebraicTopology.subordinateSet V)
      (AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V) :=
    { sup_eq := rfl
      inf_eq := (AlgebraicTopology.subordinateSet_inter U V).symm }
  exact sq.isPushout

private def subordinateCoverInclusion {X : TopCat.{u}} (U V : Set X) :
    pushout
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
        (Set.inter_subset_left : U ∩ V ⊆ U)))
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
        (Set.inter_subset_right : U ∩ V ⊆ V))) ⟶ TopCat.toSSet.obj X :=
  (subordinateCover_isPushout U V).isoPushout.inv ≫
    (AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V).ι

private instance subordinateCoverInclusion_mono {X : TopCat.{u}} (U V : Set X) :
    Mono (subordinateCoverInclusion U V) := by
  unfold subordinateCoverInclusion
  infer_instance

@[reassoc]
private theorem subordinateCoverInclusion_left {X : TopCat.{u}} (U V : Set X) :
    pushout.inl _ _ ≫ subordinateCoverInclusion U V = (AlgebraicTopology.subordinateSet U).ι := by
  rw [subordinateCoverInclusion, ← Category.assoc, IsPushout.inl_isoPushout_inv,
    SSet.Subcomplex.homOfLE_ι]

@[reassoc]
private theorem subordinateCoverInclusion_right {X : TopCat.{u}} (U V : Set X) :
    pushout.inr _ _ ≫ subordinateCoverInclusion U V = (AlgebraicTopology.subordinateSet V).ι := by
  rw [subordinateCoverInclusion, ← Category.assoc, IsPushout.inr_isoPushout_inv,
    SSet.Subcomplex.homOfLE_ι]

private theorem subordinateCoverInclusion_weak {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ) :
    WeakEquivalence (subordinateCoverInclusion (U : Set X) V) := by
  have wι : WeakEquivalence
      (AlgebraicTopology.subordinateSet (U : Set X) ⊔
          AlgebraicTopology.subordinateSet (V : Set X)).ι := by
    rw [weakEquivalence_iff]
    change weakHomotopyEquivalences (SSet.toTop.map
      (AlgebraicTopology.subordinateSet (U : Set X) ⊔
          AlgebraicTopology.subordinateSet (V : Set X)).ι)
    exact weakHomotopyEquivalences.of_postcomp _ _
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X)
      (realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences U V hcover)
  let _ := wι
  unfold subordinateCoverInclusion
  infer_instance

private abbrev subordinateCoverComparison {X : TopCat.{u}} (U V : Set X) :=
  SSet.toTop.map (subordinateCoverInclusion U V) ≫ sSetTopAdj.counit.app X

private theorem subordinateCoverComparison_weak {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ) :
    weakHomotopyEquivalences (subordinateCoverComparison (U : Set X) V) := by
  let _ : WeakEquivalence (subordinateCoverInclusion (U : Set X) V) :=
    subordinateCoverInclusion_weak U V hcover
  exact weakHomotopyEquivalences.comp_mem _ _
    (SSet.toTop_map_weak _) (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X)

@[reassoc]
private theorem subordinateCoverComparison_left {X : TopCat.{u}} (U V : Set X) :
    SSet.toTop.map (pushout.inl _ _) ≫ subordinateCoverComparison U V =
      realizedSubordinateSetEvaluation U ≫ AlgebraicTopology.subspaceIncl U := by
  rw [subordinateCoverComparison, ← Category.assoc, ← SSet.toTop.map_comp,
    subordinateCoverInclusion_left]
  exact (realizedSubordinateSetEvaluation_inclusion U).symm

@[reassoc]
private theorem subordinateCoverComparison_right {X : TopCat.{u}} (U V : Set X) :
    SSet.toTop.map (pushout.inr _ _) ≫ subordinateCoverComparison U V =
      realizedSubordinateSetEvaluation V ≫ AlgebraicTopology.subspaceIncl V := by
  rw [subordinateCoverComparison, ← Category.assoc, ← SSet.toTop.map_comp,
    subordinateCoverInclusion_right]
  exact (realizedSubordinateSetEvaluation_inclusion V).symm

private abbrev subordinateCoverProjection {E B : TopCat.{u}}
    (p : E ⟶ B) (U V : Set B) :
    pushout
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
        (Set.inter_subset_left : p ⁻¹' U ∩ p ⁻¹' V ⊆ p ⁻¹' U)))
      (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
        (Set.inter_subset_right : p ⁻¹' U ∩ p ⁻¹' V ⊆ p ⁻¹' V))) ⟶
      pushout
        (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
          (Set.inter_subset_left : U ∩ V ⊆ U)))
        (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
          (Set.inter_subset_right : U ∩ V ⊆ V))) :=
  SSet.spanPushoutProjection
    (subordinateRestriction_nested_square p (Set.inter_subset_left : U ∩ V ⊆ U))
    (subordinateRestriction_nested_square p (Set.inter_subset_right : U ∩ V ⊆ V))

private theorem subordinateCoverProjection_comm {E B : TopCat.{u}}
    (p : E ⟶ B) (U V : Set B) :
    subordinateCoverInclusion (p ⁻¹' U) (p ⁻¹' V) ≫ TopCat.toSSet.map p =
      subordinateCoverProjection p U V ≫ subordinateCoverInclusion U V := by
  apply (IsPushout.of_hasPushout _ _).hom_ext
  · have hc := SSet.spanPushoutProjection_left_assoc
      (subordinateRestriction_nested_square p (Set.inter_subset_left : U ∩ V ⊆ U))
      (subordinateRestriction_nested_square p (Set.inter_subset_right : U ∩ V ⊆ V))
      (subordinateCoverInclusion U V)
    have ht := congrArg (fun f => subordinateRestrictionProjection p U ≫ f)
      (subordinateCoverInclusion_left U V)
    have hc' := hc.trans (by simpa only [Category.assoc] using ht)
    exact (subordinateCoverInclusion_left_assoc (p ⁻¹' U) (p ⁻¹' V)
      (TopCat.toSSet.map p)).trans ((subordinateRestrictionProjection_ι p U).symm.trans hc'.symm)
  · have hc := SSet.spanPushoutProjection_right_assoc
      (subordinateRestriction_nested_square p (Set.inter_subset_left : U ∩ V ⊆ U))
      (subordinateRestriction_nested_square p (Set.inter_subset_right : U ∩ V ⊆ V))
      (subordinateCoverInclusion U V)
    have ht := congrArg (fun f => subordinateRestrictionProjection p V ≫ f)
      (subordinateCoverInclusion_right U V)
    have hc' := hc.trans (by simpa only [Category.assoc] using ht)
    exact (subordinateCoverInclusion_right_assoc (p ⁻¹' U) (p ⁻¹' V)
      (TopCat.toSSet.map p)).trans ((subordinateRestrictionProjection_ι p V).symm.trans hc'.symm)

private theorem subordinateCoverProjection_realized_comm {E B : TopCat.{u}}
    (p : E ⟶ B) (U V : Set B) :
    SSet.toTop.map (subordinateCoverInclusion (p ⁻¹' U) (p ⁻¹' V)) ≫
        (sSetTopAdj.counit.app E ≫ p) =
      SSet.toTop.map (subordinateCoverProjection p U V) ≫ subordinateCoverComparison U V := by
  have hn : sSetTopAdj.counit.app E ≫ p =
      SSet.toTop.map (TopCat.toSSet.map p) ≫ sSetTopAdj.counit.app B := by
    simpa only [Functor.id_map, Functor.comp_map] using (sSetTopAdj.counit.naturality p).symm
  have h := congrArg (fun f => SSet.toTop.map f ≫ sSetTopAdj.counit.app B)
    (subordinateCoverProjection_comm p U V)
  simpa only [SSet.toTop.map_comp, Category.assoc, hn] using h

/-- Actual homotopy-cartesian descent for two open sets. Weak comparisons on
the two overlap-to-member squares make the two member-to-global comparisons weak. -/
theorem homotopyPullbackComparison_mem_of_twoSetOpenCover {E B : TopCat.{u}}
    (p : E ⟶ B) (U V : TopologicalSpace.Opens B)
    (hcover : (U : Set B) ∪ V = Set.univ)
    (hleft : weakHomotopyEquivalences (homotopyPullbackComparison
      (restrictionProjection_nested_isPullback p
          (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U)).toCommSq))
    (hright : weakHomotopyEquivalences (homotopyPullbackComparison
      (restrictionProjection_nested_isPullback p
          (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V)).toCommSq)) :
    weakHomotopyEquivalences (homotopyPullbackComparison
      (restrictionProjection_isPullback p (U : Set B)).toCommSq) ∧
    weakHomotopyEquivalences (homotopyPullbackComparison
      (restrictionProjection_isPullback p (V : Set B)).toCommSq) := by
  let EU : TopologicalSpace.Opens E := ⟨p ⁻¹' (U : Set B), U.isOpen.preimage p.hom.continuous⟩
  let EV : TopologicalSpace.Opens E := ⟨p ⁻¹' (V : Set B), V.isOpen.preimage p.hom.continuous⟩
  have hecover : (EU : Set E) ∪ EV = Set.univ := by
    change p ⁻¹' (U : Set B) ∪ p ⁻¹' (V : Set B) = Set.univ
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  let p₀ := subordinateRestrictionProjection p ((U : Set B) ∩ V)
  let p₁ := subordinateRestrictionProjection p (U : Set B)
  let p₂ := subordinateRestrictionProjection p (V : Set B)
  let f₁ := SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
    (Set.preimage_mono (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U) :
      p ⁻¹' ((U : Set B) ∩ V) ⊆ p ⁻¹' (U : Set B)))
  let f₂ := SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
    (Set.preimage_mono (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V) :
      p ⁻¹' ((U : Set B) ∩ V) ⊆ p ⁻¹' (V : Set B)))
  let h₁ := SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
    (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U))
  let h₂ := SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono
    (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V))
  let sq₁ := subordinateRestriction_nested_square p (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U)
  let sq₂ := subordinateRestriction_nested_square p (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V)
  let a : pushout f₁ f₂ ⟶ TopCat.toSSet.obj E :=
    subordinateCoverInclusion (p ⁻¹' (U : Set B)) (p ⁻¹' (V : Set B))
  let b : SSet.toTop.obj (pushout h₁ h₂) ⟶ B := subordinateCoverComparison (U : Set B) V
  let P := sSetTopAdj.counit.app E ≫ p
  let _ : Mono a := subordinateCoverInclusion_mono (p ⁻¹' (U : Set B)) (p ⁻¹' (V : Set B))
  let _ : WeakEquivalence a := subordinateCoverInclusion_weak EU EV hecover
  have wb : weakHomotopyEquivalences b := subordinateCoverComparison_weak U V hcover
  have compat := subordinateCoverProjection_realized_comm p (U : Set B) V
  let front₁ := SSet.realized_span_front_left_square sq₁ sq₂ a b P compat
  let front₂ := SSet.realized_span_front_right_square sq₁ sq₂ a b P compat
  obtain ⟨wfront₁, wfront₂⟩ := SSet.realized_front_comparisons_weak
    p₀ p₁ p₂ f₁ f₂ h₁ h₂ sq₁.w sq₂.w a b wb P compat front₁ front₂
    (subordinateRestriction_back_comparison_weak p Set.inter_subset_left hleft)
    (subordinateRestriction_back_comparison_weak p Set.inter_subset_right hright)
  constructor
  · exact (homotopyPullbackComparison_weak_iff_of_map front₁
      (restrictionProjection_isPullback p (U : Set B)).toCommSq
      (realizedSubordinateSetEvaluation (p ⁻¹' (U : Set B)))
      (sSetTopAdj.counit.app E) (realizedSubordinateSetEvaluation (U : Set B)) (𝟙 B)
      (by
        change SSet.toTop.map (pushout.inl _ _ ≫ subordinateCoverInclusion
          (p ⁻¹' (U : Set B)) (p ⁻¹' (V : Set B))) ≫ sSetTopAdj.counit.app E = _
        rw [subordinateCoverInclusion_left]
        exact (realizedSubordinateSetEvaluation_inclusion (p ⁻¹' (U : Set B))).symm)
      (subordinateRestrictionProjection_evaluation p (U : Set B))
      (by simp only [Category.comp_id, P])
      (by
        rw [Category.comp_id]
        exact subordinateCoverComparison_left (U : Set B) V)
      (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences E)
      (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
      (weakHomotopyEquivalences.of_isIso _)).mp wfront₁
  · exact (homotopyPullbackComparison_weak_iff_of_map front₂
      (restrictionProjection_isPullback p (V : Set B)).toCommSq
      (realizedSubordinateSetEvaluation (p ⁻¹' (V : Set B)))
      (sSetTopAdj.counit.app E) (realizedSubordinateSetEvaluation (V : Set B)) (𝟙 B)
      (by
        change SSet.toTop.map (pushout.inr _ _ ≫ subordinateCoverInclusion
          (p ⁻¹' (U : Set B)) (p ⁻¹' (V : Set B))) ≫ sSetTopAdj.counit.app E = _
        rw [subordinateCoverInclusion_right]
        exact (realizedSubordinateSetEvaluation_inclusion (p ⁻¹' (V : Set B))).symm)
      (subordinateRestrictionProjection_evaluation p (V : Set B))
      (by simp only [Category.comp_id, P])
      (by
        rw [Category.comp_id]
        exact subordinateCoverComparison_right (U : Set B) V)
      (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences E)
      (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences _)
      (weakHomotopyEquivalences.of_isIso _)).mp wfront₂

private theorem homotopyPullbackRight_fibration {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) : Fibration (homotopyPullbackRight p h) :=
  HomotopyPullbackMappingPath.rightProjection_fibration p h

private def homotopyPullbackLift {A E W B : TopCat.{u}} {p : E ⟶ B} {h : W ⟶ B}
    (l : A ⟶ E) (r : A ⟶ W) (γ : A ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    A ⟶ homotopyPullback p h :=
  pullback.lift (prod.lift l r) γ (by
    apply prod.hom_ext
    · simpa [pathEndpoints, Category.assoc] using h₀.symm
    · simpa [pathEndpoints, Category.assoc] using h₁.symm)

@[reassoc]
private theorem homotopyPullbackLift_left {A E W B : TopCat.{u}} {p : E ⟶ B} {h : W ⟶ B}
    (l : A ⟶ E) (r : A ⟶ W) (γ : A ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    homotopyPullbackLift l r γ h₀ h₁ ≫ homotopyPullbackLeft p h = l := by
  rw [homotopyPullbackLift, homotopyPullbackLeft, ← Category.assoc, pullback.lift_fst]
  exact prod.lift_fst l r

@[reassoc]
private theorem homotopyPullbackLift_right {A E W B : TopCat.{u}} {p : E ⟶ B} {h : W ⟶ B}
    (l : A ⟶ E) (r : A ⟶ W) (γ : A ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    homotopyPullbackLift l r γ h₀ h₁ ≫ homotopyPullbackRight p h = r := by
  rw [homotopyPullbackLift, homotopyPullbackRight, ← Category.assoc, pullback.lift_fst]
  exact prod.lift_snd l r

@[reassoc]
private theorem homotopyPullbackLift_path {A E W B : TopCat.{u}} {p : E ⟶ B} {h : W ⟶ B}
    (l : A ⟶ E) (r : A ⟶ W) (γ : A ⟶ pathObject B)
    (h₀ : γ ≫ pathEvalZero B = l ≫ p) (h₁ : γ ≫ pathEvalOne B = r ≫ h) :
    homotopyPullbackLift l r γ h₀ h₁ ≫ homotopyPullbackPath p h = γ := by
  rw [homotopyPullbackLift, pullback.lift_snd]

private abbrev homotopyPullbackPointFiber {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :=
  pullback (homotopyPullbackRight p h) (TopCat.const (X := TopCat.of PUnit) w)

private def homotopyPullbackPointFiberToHomotopyFiber {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyPullbackPointFiber p h w ⟶ homotopyFiber p (h w) :=
  homotopyPullbackLift
    (pullback.fst _ _ ≫ homotopyPullbackLeft p h) (pullback.snd _ _)
    (pullback.fst _ _ ≫ homotopyPullbackPath p h)
    (by simp only [Category.assoc, homotopyPullbackPath_evalZero])
    (by
      have hc : TopCat.const (X := TopCat.of PUnit) w ≫ h =
          TopCat.const (X := TopCat.of PUnit) (h w) := by ext x; rfl
      rw [Category.assoc, homotopyPullbackPath_evalOne, ← Category.assoc,
        pullback.condition, Category.assoc, hc])

@[reassoc]
private theorem homotopyPullbackPointFiberToHomotopyFiber_toTotal {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyPullbackPointFiberToHomotopyFiber p h w ≫ homotopyFiberToTotal p (h w) =
      pullback.fst _ _ ≫ homotopyPullbackLeft p h := by
  rw [homotopyPullbackPointFiberToHomotopyFiber, homotopyPullbackLift_left]

@[reassoc]
private theorem homotopyPullbackPointFiberToHomotopyFiber_path {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyPullbackPointFiberToHomotopyFiber p h w ≫ homotopyFiberPath p (h w) =
      pullback.fst _ _ ≫ homotopyPullbackPath p h := by
  rw [homotopyPullbackPointFiberToHomotopyFiber, homotopyPullbackLift_path]

private def homotopyFiberToHomotopyPullbackPoint {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyFiber p (h w) ⟶ homotopyPullback p h :=
  homotopyPullbackLift (homotopyFiberToTotal p (h w)) (TopCat.const w)
    (homotopyFiberPath p (h w))
    (homotopyPullbackPath_evalZero p (TopCat.const (X := TopCat.of PUnit) (h w)))
    (by rw [homotopyPullbackPath_evalOne]; ext z; rfl)

@[reassoc]
private theorem homotopyFiberToHomotopyPullbackPoint_left {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyFiberToHomotopyPullbackPoint p h w ≫ homotopyPullbackLeft p h =
      homotopyFiberToTotal p (h w) := by
  rw [homotopyFiberToHomotopyPullbackPoint, homotopyPullbackLift_left]

@[reassoc]
private theorem homotopyFiberToHomotopyPullbackPoint_right {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyFiberToHomotopyPullbackPoint p h w ≫ homotopyPullbackRight p h = TopCat.const w := by
  rw [homotopyFiberToHomotopyPullbackPoint, homotopyPullbackLift_right]

@[reassoc]
private theorem homotopyFiberToHomotopyPullbackPoint_path {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyFiberToHomotopyPullbackPoint p h w ≫ homotopyPullbackPath p h =
      homotopyFiberPath p (h w) := by
  rw [homotopyFiberToHomotopyPullbackPoint, homotopyPullbackLift_path]

private def homotopyPullbackPointFiberFromHomotopyFiber {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyFiber p (h w) ⟶ homotopyPullbackPointFiber p h w :=
  pullback.lift (homotopyFiberToHomotopyPullbackPoint p h w) (isTerminalPUnit.from _) (by
    rw [homotopyFiberToHomotopyPullbackPoint_right]
    ext z
    rfl)

@[reassoc]
private theorem homotopyPullbackPointFiberFromHomotopyFiber_fst {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyPullbackPointFiberFromHomotopyFiber p h w ≫ pullback.fst _ _ =
      homotopyFiberToHomotopyPullbackPoint p h w := by
  rw [homotopyPullbackPointFiberFromHomotopyFiber, pullback.lift_fst]

private def homotopyPullbackPointFiberIso {E W B : TopCat.{u}}
    (p : E ⟶ B) (h : W ⟶ B) (w : W) :
    homotopyPullbackPointFiber p h w ≅ homotopyFiber p (h w) where
  hom := homotopyPullbackPointFiberToHomotopyFiber p h w
  inv := homotopyPullbackPointFiberFromHomotopyFiber p h w
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, homotopyPullbackPointFiberFromHomotopyFiber_fst,
        Category.id_comp]
      apply homotopyPullback_hom_ext
      · rw [Category.assoc, homotopyFiberToHomotopyPullbackPoint_left,
          homotopyPullbackPointFiberToHomotopyFiber_toTotal]
      · rw [Category.assoc, homotopyFiberToHomotopyPullbackPoint_right, pullback.condition]
        ext z
        rfl
      · rw [Category.assoc, homotopyFiberToHomotopyPullbackPoint_path,
          homotopyPullbackPointFiberToHomotopyFiber_path]
    · exact isTerminalPUnit.hom_ext _ _
  inv_hom_id := by
    apply homotopyPullback_hom_ext
    · simp only [Category.assoc, homotopyPullbackPointFiberToHomotopyFiber_toTotal,
        homotopyPullbackPointFiberFromHomotopyFiber_fst_assoc,
        homotopyFiberToHomotopyPullbackPoint_left, Category.id_comp]
    · exact isTerminalPUnit.hom_ext _ _
    · simp only [Category.assoc, homotopyPullbackPointFiberToHomotopyFiber_path,
        homotopyPullbackPointFiberFromHomotopyFiber_fst_assoc,
        homotopyFiberToHomotopyPullbackPoint_path, Category.id_comp]

private def comparisonStrictFiberMap {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    pullback q (TopCat.const (X := TopCat.of PUnit) w) ⟶ homotopyPullbackPointFiber p h w :=
  strictFiberMapOfSquare (p := q) (q := homotopyPullbackRight p h)
    (homotopyPullbackComparison sq) (𝟙 W)
    (by simp only [Category.comp_id, homotopyPullbackComparison_right]) w

@[reassoc]
private theorem comparisonStrictFiberMap_fst {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    comparisonStrictFiberMap sq w ≫ pullback.fst _ _ =
      pullback.fst q (TopCat.const (X := TopCat.of PUnit) w) ≫ homotopyPullbackComparison sq := by
  exact strictFiberMapOfSquare_fst (p := q) (q := homotopyPullbackRight p h)
    (homotopyPullbackComparison sq) (𝟙 W)
    (by simp only [Category.comp_id, homotopyPullbackComparison_right]) w

@[reassoc]
private theorem strictFiberToHomotopyFiber_path_total {E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) :
    strictFiberToHomotopyFiber p b ≫ homotopyFiberPath p b =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) ≫ p ≫ pathConstant B := by
  rw [← homotopyPullbackComparison_pointFiber, homotopyPullbackComparison_path]

private theorem comparisonStrictFiberMap_pointFiberIso {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    comparisonStrictFiberMap sq w ≫ (homotopyPullbackPointFiberIso p h w).hom =
      strictFiberMapOfSquare s h sq.w.symm w ≫ strictFiberToHomotopyFiber p (h w) := by
  change comparisonStrictFiberMap sq w ≫ homotopyPullbackPointFiberToHomotopyFiber p h w = _
  apply homotopyPullback_hom_ext
  · simp only [Category.assoc, homotopyPullbackPointFiberToHomotopyFiber_toTotal,
      comparisonStrictFiberMap_fst_assoc, homotopyPullbackComparison_left,
      strictFiberToHomotopyFiber_toTotal, strictFiberMapOfSquare_fst]
  · exact isTerminalPUnit.hom_ext _ _
  · simp only [Category.assoc, homotopyPullbackPointFiberToHomotopyFiber_path,
      comparisonStrictFiberMap_fst_assoc, homotopyPullbackComparison_path,
      strictFiberToHomotopyFiber_path_total, strictFiberMapOfSquare_fst_assoc]

private abbrev comparisonHomotopyFiberMap {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    homotopyFiber q w ⟶ homotopyFiber (homotopyPullbackRight p h) w :=
  homotopyFiberMapOfSquare (p := q) (q := homotopyPullbackRight p h)
    (homotopyPullbackComparison sq) (𝟙 W)
    (by simp only [Category.comp_id, homotopyPullbackComparison_right]) w

private theorem comparisonStrictFiberMap_naturality {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    comparisonStrictFiberMap sq w ≫ strictFiberToHomotopyFiber (homotopyPullbackRight p h) w =
      strictFiberToHomotopyFiber q w ≫ comparisonHomotopyFiberMap sq w :=
  strictFiberToHomotopyFiber_naturality (p := q) (q := homotopyPullbackRight p h)
    (homotopyPullbackComparison sq) (𝟙 W)
    (by simp only [Category.comp_id, homotopyPullbackComparison_right]) w

private theorem comparisonHomotopyFiberMap_weak {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W)
    (wc : weakHomotopyEquivalences (homotopyPullbackComparison sq)) :
    weakHomotopyEquivalences (comparisonHomotopyFiberMap sq w) :=
  homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences
    (p := q) (q := homotopyPullbackRight p h)
    (homotopyPullbackComparison sq) (𝟙 W)
    (by simp only [Category.comp_id, homotopyPullbackComparison_right]) w
    wc (weakHomotopyEquivalences.of_isIso _)

private theorem comparison_mem_of_isPullback_comparisons {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : IsPullback s q p h)
    (hlocal : ∀ w : W, weakHomotopyEquivalences (strictFiberToHomotopyFiber q w))
    (htarget : ∀ w : W, weakHomotopyEquivalences (strictFiberToHomotopyFiber p (h w))) :
    weakHomotopyEquivalences (homotopyPullbackComparison sq.toCommSq) := by
  let _ : Fibration (homotopyPullbackRight p h) := homotopyPullbackRight_fibration p h
  apply mem_weakHomotopyEquivalences_of_homotopyFiberMaps q (homotopyPullbackRight p h)
    (homotopyPullbackComparison sq.toCommSq) (homotopyPullbackComparison_right sq.toCommSq)
  intro w
  let _ : IsIso (strictFiberMapOfSquare s h sq.w.symm w) :=
    isIso_strictFiberMapOfSquare_of_isPullback sq w
  have ws : weakHomotopyEquivalences (comparisonStrictFiberMap sq.toCommSq w) := by
    apply weakHomotopyEquivalences.of_postcomp _ _
      (weakHomotopyEquivalences.of_isIso (homotopyPullbackPointFiberIso p h w).hom)
    rw [comparisonStrictFiberMap_pointFiberIso]
    exact weakHomotopyEquivalences.comp_mem _ _ (weakHomotopyEquivalences.of_isIso _)
      (htarget w)
  have wf : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber q w ≫ comparisonHomotopyFiberMap sq.toCommSq w) := by
    rw [← comparisonStrictFiberMap_naturality]
    exact weakHomotopyEquivalences.comp_mem _ _ ws
      (strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences (homotopyPullbackRight p h) w)
  exact weakHomotopyEquivalences.of_precomp _ _ (hlocal w) wf

private theorem targetComparison_mem_of_isPullback_comparison {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : IsPullback s q p h) (w : W)
    (wc : weakHomotopyEquivalences (homotopyPullbackComparison sq.toCommSq))
    (hlocal : weakHomotopyEquivalences (strictFiberToHomotopyFiber q w)) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p (h w)) := by
  let _ : Fibration (homotopyPullbackRight p h) := homotopyPullbackRight_fibration p h
  have wq := strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences (homotopyPullbackRight p h) w
  have wf := comparisonHomotopyFiberMap_weak sq.toCommSq w wc
  have ws : weakHomotopyEquivalences (comparisonStrictFiberMap sq.toCommSq w) := by
    apply weakHomotopyEquivalences.of_postcomp _ _ wq
    rw [comparisonStrictFiberMap_naturality]
    exact weakHomotopyEquivalences.comp_mem _ _ hlocal wf
  let _ : IsIso (strictFiberMapOfSquare s h sq.w.symm w) :=
    isIso_strictFiberMapOfSquare_of_isPullback sq w
  apply weakHomotopyEquivalences.of_precomp _ _ (weakHomotopyEquivalences.of_isIso
    (strictFiberMapOfSquare s h sq.w.symm w))
  rw [← comparisonStrictFiberMap_pointFiberIso sq.toCommSq w]
  exact weakHomotopyEquivalences.comp_mem _ _ ws
    (weakHomotopyEquivalences.of_isIso (homotopyPullbackPointFiberIso p h w).hom)

/-- The two-open-set quasifibration criterion for the actual constant-path
strict-to-homotopy-fiber comparison. All three hypotheses are comparisons
for the actual restrictions over the two opens and their intersection. -/
theorem strictFiberToHomotopyFiber_mem_of_twoSetOpenCover {E B : TopCat.{u}}
    (p : E ⟶ B) (U V : TopologicalSpace.Opens B)
    (hcover : (U : Set B) ∪ V = Set.univ)
    (hU : ∀ u : TopCat.of (U : Set B), weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p (U : Set B)) u))
    (hV : ∀ v : TopCat.of (V : Set B), weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p (V : Set B)) v))
    (hUV : ∀ w : TopCat.of ((U : Set B) ∩ V : Set B), weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p ((U : Set B) ∩ V)) w))
    (b : B) : weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  have wleft := comparison_mem_of_isPullback_comparisons
    (restrictionProjection_nested_isPullback p (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U))
    hUV (fun w => hU (AlgebraicTopology.subspaceInclOfSubset Set.inter_subset_left w))
  have wright := comparison_mem_of_isPullback_comparisons
    (restrictionProjection_nested_isPullback p (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V))
    hUV (fun w => hV (AlgebraicTopology.subspaceInclOfSubset Set.inter_subset_right w))
  obtain ⟨wU, wV⟩ := homotopyPullbackComparison_mem_of_twoSetOpenCover p U V hcover wleft wright
  have hb : b ∈ (U : Set B) ∪ V := hcover.symm ▸ Set.mem_univ b
  rcases hb with hb | hb
  · exact targetComparison_mem_of_isPullback_comparison
      (restrictionProjection_isPullback p (U : Set B)) ⟨b, hb⟩ wU (hU ⟨b, hb⟩)
  · exact targetComparison_mem_of_isPullback_comparison
      (restrictionProjection_isPullback p (V : Set B)) ⟨b, hb⟩ wV (hV ⟨b, hb⟩)

end TopCat

end
