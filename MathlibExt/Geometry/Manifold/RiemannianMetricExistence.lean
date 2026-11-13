/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

open Manifold
private lemma perCenterContMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (e0 : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (c x₀ : M) (hx₀ : x₀ ∈ (chartAt H c).source)
    (G : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hG : ∀ (x : M) (v w : TangentSpace I x),
      G x v w = @inner ℝ _ _
        (((e0.toContinuousLinearMap).comp
          ((trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearMapAt ℝ x)) v)
        (((e0.toContinuousLinearMap).comp
          ((trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearMapAt ℝ x)) w)) :
    ContMDiffWithinAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (G y))
      (chartAt H c).source x₀ := by
  haveI h1 : IsManifold I 1 M :=
    IsManifold.of_le (n := (⊤ : ℕ∞)) (m := 1) (by simp)
  haveI hTan : ContMDiffVectorBundle (⊤ : ℕ∞) E (fun y : M => TangentSpace I y) I :=
    inferInstance
  haveI h1m : MemTrivializationAtlas
      (trivializationAt E (fun (x : M) => TangentSpace I x) x₀) := inferInstance
  haveI h2m : MemTrivializationAtlas
      (trivializationAt E (fun (x : M) => TangentSpace I x) c) := inferInstance
  refine (Bundle.contMDiffWithinAt_section).mpr ?_
  set T : M → (E →L[ℝ] E) := fun y =>
    ((Bundle.Trivialization.coordChangeL ℝ
      (trivializationAt E (fun (x : M) => TangentSpace I x) x₀)
      (trivializationAt E (fun (x : M) => TangentSpace I x) c) y : E ≃L[ℝ] E) : E →L[ℝ] E) with hT
  set B₀ : E →L[ℝ] E →L[ℝ] ℝ :=
    (((ContinuousLinearMap.compL ℝ E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ).flip
      e0.toContinuousLinearMap).comp
      ((innerSL ℝ).comp e0.toContinuousLinearMap)) with hB₀
  have hTbase : (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet =
      (chartAt H c).source := TangentBundle.trivializationAt_baseSet c
  have hx0c : x₀ ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet := by
    rw [hTbase]; exact hx₀
  have hx0x : x₀ ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hTOn : ContMDiffOn I (modelWithCornersSelf ℝ (E →L[ℝ] E)) (⊤ : ℕ∞) T
      ((trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∩
        (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet) :=
    ContMDiffVectorBundle.contMDiffOn_coordChangeL
      (trivializationAt E (fun (x : M) => TangentSpace I x) x₀)
      (trivializationAt E (fun (x : M) => TangentSpace I x) c)
  have hTW : ContMDiffWithinAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) (⊤ : ℕ∞) T
      (chartAt H c).source x₀ := by
    have hmem : x₀ ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∩
        (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet :=
      ⟨hx0x, hx0c⟩
    have hwithin := hTOn x₀ hmem
    apply hwithin.mono_of_mem_nhdsWithin ?_
    have hUopen : IsOpen (chartAt H c).source := (chartAt H c).open_source
    have hUnb : (chartAt H c).source ∈ nhds x₀ := hUopen.mem_nhds hx₀
    have hnb : (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∈ nhds x₀ :=
      (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).open_baseSet.mem_nhds hx0x
    have hinter : (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∩
        (chartAt H c).source ∈ nhds x₀ :=
      Filter.inter_mem hnb hUnb
    have hnhds : (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∩
        (chartAt H c).source ∈ nhdsWithin x₀ (chartAt H c).source :=
      mem_nhdsWithin_of_mem_nhds hinter
    rw [hTbase]
    exact hnhds
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun U : E →L[ℝ] E =>
      (((ContinuousLinearMap.compL ℝ E E ℝ).flip U).comp (B₀.comp U))) := by
    fun_prop
  have hS : ContMDiffWithinAt I (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      ((fun U : E →L[ℝ] E =>
        (((ContinuousLinearMap.compL ℝ E E ℝ).flip U).comp (B₀.comp U))) ∘ T)
      (chartAt H c).source x₀ :=
    ContDiff.comp_contMDiffWithinAt hF hTW
  have hB₀apply : ∀ (a b : E),
      B₀ a b = @inner ℝ _ _ ((e0.toContinuousLinearMap) a) ((e0.toContinuousLinearMap) b) := by
    intro a b
    simp only [hB₀]
    rfl
  have hTconn : ∀ (y : M),
      y ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet →
      y ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet →
      ∀ v : E, (T y) v =
        ((trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearMapAt ℝ y)
          ((trivializationAt E (fun (x : M) => TangentSpace I x) x₀).symm y v) := by
    intro y hy1 hy2 v
    have hcc : (Bundle.Trivialization.coordChangeL ℝ
        (trivializationAt E (fun (x : M) => TangentSpace I x) x₀)
        (trivializationAt E (fun (x : M) => TangentSpace I x) c) y) v =
        ((trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearMapAt ℝ y)
          ((trivializationAt E (fun (x : M) => TangentSpace I x) x₀).symm y v) := by
      rw [Bundle.Trivialization.coordChangeL_apply
        (trivializationAt E (fun (x : M) => TangentSpace I x) x₀)
        (trivializationAt E (fun (x : M) => TangentSpace I x) c) ⟨hy1, hy2⟩ v]
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (fun (x : M) => TangentSpace I x) c) hy2]
    simp only [hT] at *
    exact hcc
  have hpt : ∀ y : M, y ∈ (chartAt H c).source →
      y ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet →
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨y, G y⟩).2 =
      (((fun U : E →L[ℝ] E =>
        (((ContinuousLinearMap.compL ℝ E E ℝ).flip U).comp (B₀.comp U))) ∘ T) y) := by
    intro y hyU hyH
    have hmemH : y ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet ∩
        (trivializationAt (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
      rwa [hom_trivializationAt_baseSet] at hyH
    have h1x : y ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) x₀).baseSet := hmemH.1
    have hyC : y ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet := by
      rw [hTbase]; exact hyU
    have h3 : y ∈ (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet := by
      simp
    ext v w
    simp only [hom_trivializationAt_apply, Function.comp_apply]
    rw [inCoordinates_apply_eq₂ h1x h1x h3]
    simp
    rw [hG, hB₀apply]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hTconn y h1x hyC v, ← hTconn y h1x hyC w]
  have hHomOpen : IsOpen (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet :=
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).open_baseSet
  have hHomMem : x₀ ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hset : (chartAt H c).source ∩
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet ∈
      nhdsWithin x₀ (chartAt H c).source := by
    have h1nb : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet ∈ nhds x₀ :=
      hHomOpen.mem_nhds hHomMem
    have hUopen : IsOpen (chartAt H c).source := (chartAt H c).open_source
    have hUnb : (chartAt H c).source ∈ nhds x₀ := hUopen.mem_nhds hx₀
    have hinter : (chartAt H c).source ∩
        (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet ∈ nhds x₀ :=
      Filter.inter_mem hUnb h1nb
    exact mem_nhdsWithin_of_mem_nhds hinter
  have heq : (fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, G x⟩).2) =ᶠ[nhdsWithin x₀ (chartAt H c).source]
      (((fun U : E →L[ℝ] E =>
        (((ContinuousLinearMap.compL ℝ E E ℝ).flip U).comp (B₀.comp U))) ∘ T)) :=
    Filter.eventuallyEq_of_mem hset (fun y hy => hpt y hy.1 hy.2)
  have hval : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x₀, G x₀⟩).2 =
      (((fun U : E →L[ℝ] E =>
        (((ContinuousLinearMap.compL ℝ E E ℝ).flip U).comp (B₀.comp U))) ∘ T) x₀) :=
    hpt x₀ hx₀ hHomMem
  exact ContMDiffWithinAt.congr_of_eventuallyEq hS heq hval

/-- Gluing step: a locally finite partition-of-unity sum of smooth Hom-bundle sections,
each smooth on its chart source containing the corresponding `tsupport`, is smooth.
Placed before `open Bundle` so that Hom-bundle instance synthesis avoids the costly
scoped `Bundle` instances. -/
private lemma finsumSectionSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M))
    (G : (j : M) → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hG_on : ∀ (j : M), ContMDiffOn I
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (G j y))
      (chartAt H j).source)
    (hsub : ∀ (j : M), tsupport (ρ j) ⊆ (chartAt H j).source) :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun b => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (∑ᶠ j, (ρ j b) • G j b)) := by
  haveI h1 : IsManifold I 1 M :=
    IsManifold.of_le (n := (⊤ : ℕ∞)) (m := 1) (by simp)
  have hterm : ∀ (j : M), ContMDiff I
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun x => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x ((ρ j x) • G j x)) := by
    intro j
    exact ContMDiffOn.smul_section_of_tsupport
      (((ρ j).contMDiff).of_le le_rfl).contMDiffOn
      (chartAt H j).open_source (hsub j) (hG_on j)
  have hlf : LocallyFinite fun j => {x : M | (ρ j x) • G j x ≠ 0} := by
    apply ρ.locallyFinite.subset (fun j x hx => ?_)
    rw [Function.mem_support]
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hcon
    apply hx
    rw [hcon]
    ext v w
    simp
  exact ContMDiff.finsum_section_of_locallyFinite hlf (fun j => hterm j)

@[expose] public section

noncomputable section

open Bundle Manifold

namespace MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted
/--
**Existence of Riemannian metrics.** Let $E$ be a finite-dimensional real normed space and let
$M$ be a Hausdorff, second-countable $C^\infty$ manifold modeled on $E$ (possibly with boundary
or corners). Then $M$ admits a $C^\infty$ Riemannian metric on its tangent bundle.

Proves `Wanted` entry `riemannianMetricExistence`.

Source: J. Lee, Introduction to Smooth Manifolds, 2nd ed.
existence of Riemannian metrics via partition of unity; also Lee, Riemannian Manifolds; Lean
states finite-dimensional Hausdorff second-countable specialization.
-/

theorem riemannianMetricExistence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    : Nonempty (Bundle.ContMDiffRiemannianMetric I (⊤ : ℕ∞) E (fun (x : M) => TangentSpace I x)) := by
  haveI h1 : IsManifold I 1 M :=
    IsManifold.of_le (n := (⊤ : ℕ∞)) (m := 1) (by simp)
  haveI hH : LocallyCompactSpace H := I.locallyCompactSpace
  haveI hM : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI hS : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
      Module.finrank ℝ E := by simp
  obtain ⟨e0⟩ : Nonempty (E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hfin.symm
  set L : (c : M) → (x : M) → (TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    fun c x => (e0.toContinuousLinearMap).comp
      ((trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearMapAt ℝ x) with hL
  set G : (c : M) → (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun c x =>
      let LE : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := L c x
      let BE : E →L[ℝ] E →L[ℝ] ℝ :=
        ((ContinuousLinearMap.compL ℝ E _ _).flip LE).comp ((innerSL ℝ).comp LE)
      BE with hG
  have hG_apply : ∀ (c x : M) (v w : TangentSpace I x),
      G c x v w = @inner ℝ _ _ (L c x v) (L c x w) := by
    intro c x v w
    simp only [hG, hL]
    rfl
  have hbase : ∀ (c : M),
      (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet =
        (chartAt H c).source := fun c => TangentBundle.trivializationAt_baseSet c
  have hL_inj : ∀ (c x : M), x ∈ (chartAt H c).source → Function.Injective (L c x) := by
    intro c x hx
    have hxB : x ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) c).baseSet := by
      rw [hbase]; exact hx
    let A : TangentSpace I x ≃L[ℝ] E :=
      (trivializationAt E (fun (x : M) => TangentSpace I x) c).continuousLinearEquivAt ℝ x hxB
    have hLeq : ∀ v : TangentSpace I x, L c x v = e0 (A v) := by
      intro v
      simp only [hL, A, ContinuousLinearMap.comp_apply,
        Trivialization.coe_continuousLinearEquivAt_eq _ hxB]
      rfl
    intro u v huv
    rw [hLeq, hLeq] at huv
    have h1 : A u = A v := e0.injective huv
    exact A.injective h1
  have hG_symm : ∀ (c x : M) (v w : TangentSpace I x), G c x v w = G c x w v := by
    intro c x v w
    rw [hG_apply, hG_apply, real_inner_comm]
  have hG_nonneg : ∀ (c x : M) (v : TangentSpace I x), 0 ≤ G c x v v := by
    intro c x v
    rw [hG_apply]
    exact real_inner_self_nonneg
  have hG_pos : ∀ (c x : M) (v : TangentSpace I x),
      x ∈ (chartAt H c).source → v ≠ 0 → 0 < G c x v v := by
    intro c x v hx hv
    rw [hG_apply]
    exact real_inner_self_pos.mpr (fun h => hv (hL_inj c x hx (by simpa using h)))
  set innerF : (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun x => ∑ᶠ j, (ρ j x) • G j x with hF
  have hinnerFin : ∀ (x : M) (v w : TangentSpace I x),
      innerF x v w = ∑ j ∈ ρ.finsupport x, ρ j x * G j x v w := by
    intro x v w
    have hbridge := ρ.sum_finsupport_smul_eq_finsum x (fun j (_ : M) => G j x)
    have h1 : innerF x = ∑ j ∈ ρ.finsupport x, (ρ j x) • G j x := by
      simp only [hF]
      rw [← hbridge]
    rw [h1]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  have hsymm : ∀ (x : M) (v w : TangentSpace I x),
      innerF x v w = innerF x w v := by
    intro x v w
    rw [hinnerFin, hinnerFin]
    apply Finset.sum_congr rfl
    intro j _
    rw [hG_symm j x v w]
  have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < innerF x v v := by
    intro x v hv
    rw [hinnerFin]
    obtain ⟨j₀, hj₀⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    have hρne : ρ j₀ x ≠ 0 := ne_of_gt hj₀
    have hj₀mem : j₀ ∈ ρ.finsupport x := by
      rw [ρ.mem_finsupport, Function.mem_support]
      exact hρne
    have hxSrc : x ∈ (chartAt H j₀).source := by
      have hmem : x ∈ tsupport (ρ j₀) :=
        subset_closure (Function.mem_support.mpr hρne)
      exact hρ j₀ hmem
    have hnn : ∀ j ∈ ρ.finsupport x, 0 ≤ ρ j x * G j x v v :=
      fun j _ => mul_nonneg (ρ.nonneg j x) (hG_nonneg j x v)
    have hone : ∃ j ∈ ρ.finsupport x, 0 < ρ j x * G j x v v :=
      ⟨j₀, hj₀mem, mul_pos hj₀ (hG_pos j₀ x v hxSrc hv)⟩
    exact Finset.sum_pos' hnn hone
  have hsingle_bound : ∀ (x j : M), x ∈ (chartAt H j).source → ρ j x ≠ 0 →
      Bornology.IsVonNBounded ℝ {v : TangentSpace I x | G j x v v < 1 / (ρ j x)} := by
    intro x j hxChart hρne
    have hxB : x ∈ (trivializationAt E (fun (x : M) => TangentSpace I x) j).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hxChart
    let A : TangentSpace I x ≃L[ℝ] E :=
      (trivializationAt E (fun (x : M) => TangentSpace I x) j).continuousLinearEquivAt ℝ x hxB
    let Φ : TangentSpace I x ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := A.trans e0
    have hL_eq : ∀ v : TangentSpace I x, L j x v = Φ v := by
      intro v
      simp only [hL, Φ, A, ContinuousLinearEquiv.trans_apply,
        Trivialization.coe_continuousLinearEquivAt_eq _ hxB]
      rfl
    have hPhi_eq : ∀ v : TangentSpace I x, G j x v v = ‖Φ v‖ ^ 2 := by
      intro v
      rw [hG_apply, hL_eq, real_inner_self_eq_norm_sq]
    have himg : Bornology.IsVonNBounded ℝ
        ((Φ.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] TangentSpace I x) ''
          Metric.closedBall 0 (max 1 (1 / (ρ j x)))) :=
      (NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_closedBall).image _
    apply Bornology.IsVonNBounded.subset (s₁ := {v : TangentSpace I x | G j x v v < 1 / (ρ j x)}) ?_ himg
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    rw [hPhi_eq] at hv
    have hnorm_le : ‖Φ v‖ ≤ max 1 (1 / (ρ j x)) := by
      by_cases h : ‖Φ v‖ ≤ 1
      · exact le_trans h (le_max_left _ _)
      · have h1lt : (1 : ℝ) < ‖Φ v‖ := not_le.mp h
        have h2 : ‖Φ v‖ < ‖Φ v‖ ^ 2 := by nlinarith [sq_nonneg (‖Φ v‖ : ℝ), norm_nonneg (Φ v)]
        have h3 : ‖Φ v‖ ^ 2 ≤ max 1 (1 / (ρ j x)) :=
          le_trans hv.le (le_max_right _ _)
        exact le_trans h2.le h3
    have hmem : Φ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (max 1 (1 / (ρ j x))) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hnorm_le
    exact ⟨Φ v, hmem, by simp [Φ]⟩
  have hbound : ∀ (b : M),
      Bornology.IsVonNBounded ℝ {v : TangentSpace I b | innerF b v v < 1} := by
    intro b
    obtain ⟨j₀, hj₀⟩ := ρ.exists_pos_of_mem (Set.mem_univ b)
    have hρne : ρ j₀ b ≠ 0 := ne_of_gt hj₀
    have hj₀mem : j₀ ∈ ρ.finsupport b := by
      rw [ρ.mem_finsupport, Function.mem_support]
      exact hρne
    have hxSrc : b ∈ (chartAt H j₀).source := by
      have hmem : b ∈ tsupport (ρ j₀) :=
        subset_closure (Function.mem_support.mpr hρne)
      exact hρ j₀ hmem
    have hsub : {v : TangentSpace I b | innerF b v v < 1} ⊆
        {v : TangentSpace I b | G j₀ b v v < 1 / (ρ j₀ b)} := by
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [hinnerFin] at hv
      have hle : ρ j₀ b * G j₀ b v v ≤
          ∑ j ∈ ρ.finsupport b, ρ j b * G j b v v :=
        Finset.single_le_sum
          (fun j _ => mul_nonneg (ρ.nonneg j b) (hG_nonneg j b v)) hj₀mem
      have hlt : ρ j₀ b * G j₀ b v v < 1 := lt_of_le_of_lt hle hv
      rw [lt_div_iff₀ hj₀]
      rw [mul_comm]
      exact hlt
    exact Bornology.IsVonNBounded.subset hsub (hsingle_bound b j₀ hxSrc hρne)
  have hG_on : ∀ (j : M), ContMDiffOn I
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (G j y))
      (chartAt H j).source := by
    intro j x₀ hx₀
    exact perCenterContMDiff e0 j x₀ hx₀ (G j) (fun x v w => by
      rw [hG_apply j x v w, hL])
  have hcont : ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun b => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (innerF b)) := by
    simp only [hF]
    exact finsumSectionSmooth ρ G hG_on hρ
  exact ⟨⟨innerF, hsymm, hpos, hbound, hcont⟩⟩

end MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted
