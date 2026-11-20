/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.PeriodicPlanarCanonicalTranslation
import Code.FK.FreeTailTriviality

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

namespace StatMech
namespace FK
namespace PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]


def PeriodicGraph.bufferedEdgeWindow (P : PeriodicGraph V) (N : ℕ) :
    Set (Sym2 V) :=
  Set.range (P.edgeIncl (P.bufferedRadius N))

theorem PeriodicGraph.bufferedEdgeWindow_mono (P : PeriodicGraph V) :
    Monotone P.bufferedEdgeWindow := by
  intro N M hNM e he
  obtain ⟨eN, rfl⟩ := he
  induction eN using Sym2.inductionOn with
  | _ x y =>
      let xM : P.BufferedVertex M := P.bufferedVertexInclLE hNM x
      let yM : P.BufferedVertex M := P.bufferedVertexInclLE hNM y
      exact ⟨s(xM, yM), rfl⟩


abbrev PeriodicGraph.IsBufferedTailEvent (P : PeriodicGraph V)
    (s : Set (ConfigSpace (Sym2 V))) : Prop :=
  AtiTailEvent P.bufferedEdgeWindow s

omit [Countable V] in
theorem PeriodicGraph.bufferedAdjMatchLE (P : PeriodicGraph V)
    {N M : ℕ} (hNM : N ≤ M) :
    ocd_AdjMatch (P.bufferedGraph N) (P.bufferedGraph M)
      (P.bufferedVertexInclLE hNM) := by
  intro x y
  rfl

omit [Countable V] in
theorem PeriodicGraph.edgeIncl_mem_bufferedEdgeWindow (P : PeriodicGraph V)
    (N : ℕ) (e : Sym2 (P.BufferedVertex N)) :
    P.edgeIncl (P.bufferedRadius N) e ∈ P.bufferedEdgeWindow N :=
  ⟨e, rfl⟩

omit [Countable V] in
theorem PeriodicGraph.edgeIncl_range_mono (P : PeriodicGraph V)
    {N M : ℕ} (hNM : N ≤ M) {e : Sym2 V}
    (he : e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    e ∈ Set.range (P.edgeIncl (P.bufferedRadius M)) := by
  obtain ⟨eN, rfl⟩ := he
  induction eN using Sym2.inductionOn with
  | _ x y =>
      let xM : P.BufferedVertex M := P.bufferedVertexInclLE hNM x
      let yM : P.BufferedVertex M := P.bufferedVertexInclLE hNM y
      exact ⟨s(xM, yM), rfl⟩



theorem PeriodicGraph.isClopen_eq_bufferedCylinder
    (P : PeriodicGraph V) (A : Set (ConfigSpace (Sym2 V))) (hA : IsClopen A) :
    ∃ (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))),
      A = P.bufferedCylinder N S ∧
        (IsIncreasing A → IsIncreasing S) := by
  classical
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hA
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges F
  let S : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
    P.extendEdge (P.bufferedRadius N) ⁻¹' A
  refine ⟨N, S, ?_, ?_⟩
  · ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage, S]
    apply hF
    intro e he
    obtain ⟨eN, heN⟩ := hN e he
    change P.extendEdge (P.bufferedRadius N)
      (P.bufferedRestrict N omega) e = omega e
    rw [← heN, P.extendEdge_edgeIncl]
    rfl
  · intro hinc omega eta home hmem
    exact hinc (P.monotone_extendEdge (P.bufferedRadius N) home) hmem



theorem PeriodicGraph.freeBufferedMeasure_inner_mul_exterior_le
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A)
    (F : Finset (Sym2 V)) (S : Set (ConfigSpace F))
    (hF : (↑F : Set (Sym2 V)) ⊆ (P.bufferedEdgeWindow N)ᶜ)
    (hrange : ∀ e ∈ F,
      e ∈ Set.range (P.edgeIncl (P.bufferedRadius m))) :
    (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A) *
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (cylinder (α := fun _ : Sym2 V => Bool) F S) ≤
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A ∩
          cylinder (α := fun _ : Sym2 V => Bool) F S) := by
  classical
  let B : Set (ConfigSpace (Sym2 (P.BufferedVertex m))) :=
    P.extendEdge (P.bufferedRadius m) ⁻¹'
      cylinder (α := fun _ : Sym2 V => Bool) F S
  have hBout : DependsOnOutside
      (ocd_innerEdgeFinset (P.bufferedVertexInclLE hNm)) B := by
    intro psi rho hagree
    change P.extendEdge (P.bufferedRadius m) psi ∈
        cylinder (α := fun _ : Sym2 V => Bool) F S ↔
      P.extendEdge (P.bufferedRadius m) rho ∈
        cylinder (α := fun _ : Sym2 V => Bool) F S
    have hrestr : F.restrict (P.extendEdge (P.bufferedRadius m) psi) =
        F.restrict (P.extendEdge (P.bufferedRadius m) rho) := by
      funext e
      obtain ⟨em, hem⟩ := hrange e.1 e.2
      have hemOut : em ∉ ocd_innerEdgeFinset
          (P.bufferedVertexInclLE hNm) := by
        intro hin
        rw [ocd_mem_innerEdgeFinset] at hin
        obtain ⟨eN, heN⟩ := hin
        have heWindow : e.1 ∈ P.bufferedEdgeWindow N := by
          refine ⟨eN, ?_⟩
          rw [← hem, ← heN]
          exact (P.edgeIncl_bufferedVertexInclLE hNm eN).symm
        exact hF e.2 heWindow
      change P.extendEdge (P.bufferedRadius m) psi e.1 =
        P.extendEdge (P.bufferedRadius m) rho e.1
      rw [← hem, P.extendEdge_edgeIncl, P.extendEdge_edgeIncl]
      exact (hagree em hemOut).symm
    simp only [mem_cylinder, hrestr]
  let Aout : Set (ConfigSpace (Sym2 (P.BufferedVertex m))) :=
    P.bufferedRestrictLE hNm ⁻¹' A
  have hfinite := freeInner_mul_outside_le_bcProb
    (P.bufferedGraph N) (P.bufferedGraph m)
    (P.bufferedVertexInclLE hNm) (P.bufferedVertexInclLE hNm).injective
    (P.bufferedAdjMatchLE hNm) (⊥ : SimpleGraph (P.BufferedVertex m))
    hp hp1 hq hA hBout
  have hBfull : cylinder (α := fun _ : Sym2 V => Bool) F S =
      P.bufferedCylinder m B :=
    P.fullCylinder_eq_bufferedCylinder m F S hrange
  have hAfull : P.bufferedCylinder N A = P.bufferedCylinder m Aout := by
    ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage, Aout]
    have hrestrict : P.bufferedRestrictLE hNm (P.bufferedRestrict m omega) =
        P.bufferedRestrict N omega := by
      funext e
      exact congrArg omega (P.edgeIncl_bufferedVertexInclLE hNm e)
    rw [hrestrict]
  have hcross : P.bufferedCylinder N A ∩
      cylinder (α := fun _ : Sym2 V => Bool) F S =
      P.bufferedCylinder m (Aout ∩ B) := by
    rw [hAfull, hBfull]
    rfl
  have hpre_refl (n : ℕ)
      (C : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))) :
      P.bufferedRestrictLE (le_refl n) ⁻¹' C = C := by
    ext omega
    simp only [Set.mem_preimage]
    have hrefl : P.bufferedRestrictLE (le_refl n) omega = omega := by
      funext e
      induction e using Sym2.inductionOn with
      | _ x y => rfl
    rw [hrefl]
  rw [hcross, hBfull,
    P.freeBufferedMeasure_real_cylinder (le_refl m) hp hp1
      (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder (le_refl m) hp hp1
      (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder (le_refl N) hp hp1
      (zero_lt_one.trans_le hq)]
  rw [hpre_refl N A, hpre_refl m B, hpre_refl m (Aout ∩ B)]
  simpa only [Aout, bcProb_bot_eq_fkProb] using hfinite



theorem PeriodicGraph.freeBufferedFinite_inner_mul_exteriorCylinder_le
    (P : PeriodicGraph V) (N : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A)
    (F : Finset (Sym2 V)) (S : Set (ConfigSpace F))
    (hF : (↑F : Set (Sym2 V)) ⊆ (P.bufferedEdgeWindow N)ᶜ) :
    (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A) *
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (cylinder (α := fun _ : Sym2 V => Bool) F S) ≤
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A ∩
          cylinder (α := fun _ : Sym2 V => Bool) F S) := by
  obtain ⟨M0, hM0⟩ := P.exists_bufferedLevel_edges F
  let c := (P.freeBufferedMeasure N hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
      (P.bufferedCylinder N A)
  have hleft : Tendsto (fun m => c *
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (cylinder (α := fun _ : Sym2 V => Bool) F S)) atTop
      (nhds (c *
        (P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (cylinder (α := fun _ : Sym2 V => Bool) F S))) :=
    (P.freeBufferedMeasure_tendsto_finiteCylinder hp hp1 hq F S).const_mul c
  have hright : Tendsto (fun m =>
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A ∩
          cylinder (α := fun _ : Sym2 V => Bool) F S)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N A ∩
            cylinder (α := fun _ : Sym2 V => Bool) F S))) :=
    (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
      ((P.bufferedCylinder_isClopen N A).inter (isClopen_cylinderEvent F S))
  have heventually : ∀ᶠ m in atTop,
      c * (P.freeBufferedMeasure m hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (cylinder (α := fun _ : Sym2 V => Bool) F S) ≤
        (P.freeBufferedMeasure m hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (P.bufferedCylinder N A ∩
              cylinder (α := fun _ : Sym2 V => Bool) F S) := by
    filter_upwards [eventually_ge_atTop (max N M0)] with m hm
    apply P.freeBufferedMeasure_inner_mul_exterior_le
      (Nat.le_max_left N M0 |>.trans hm) hp hp1 hq hA F S hF
    intro e he
    exact P.edgeIncl_range_mono (Nat.le_max_right N M0 |>.trans hm) (hM0 e he)
  exact le_of_tendsto_of_tendsto hleft hright heventually



theorem PeriodicGraph.freeBufferedFinite_inner_mul_exterior_le
    (P : PeriodicGraph V) (N : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A)
    {s : Set (ConfigSpace (Sym2 V))}
    (hs : @MeasurableSet _ (outsideSigma (P.bufferedEdgeWindow N)) s) :
    (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A) *
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N A ∩ s) := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  let c := (P.freeBufferedMeasure N hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
      (P.bufferedCylinder N A)
  let Afull := P.bufferedCylinder N A
  have hAfull : MeasurableSet Afull := P.bufferedCylinder_measurableSet N A
  have hsfull : MeasurableSet s :=
    (outsideSigma_le (P.bufferedEdgeWindow N)) s hs
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := measureReal_le_one
  by_contra hle
  have hgap : 0 < c * mu.real s - mu.real (Afull ∩ s) :=
    sub_pos.mpr (lt_of_not_ge hle)
  let delta := (c * mu.real s - mu.real (Afull ∩ s)) / 4
  have hdelta : 0 < delta := div_pos hgap (by norm_num)
  obtain ⟨F, S, hF, happrox⟩ :=
    ati_exterior_approx_cylinder (mu := mu) (P.bufferedEdgeWindow N) hs
      (ε := ENNReal.ofReal delta) (by simpa using hdelta)
  let Bfull : Set (ConfigSpace (Sym2 V)) :=
    cylinder (α := fun _ : Sym2 V => Bool) F S
  have hBfull : MeasurableSet Bfull :=
    (isClopen_cylinderEvent F S).isOpen.measurableSet
  have happReal : mu.real (s ∆ Bfull) < delta := by
    have htop : mu (s ∆ Bfull) ≠ ⊤ := measure_ne_top mu _
    have h := (ENNReal.toReal_lt_toReal htop (by simp)).2 happrox
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  have hineq : c * mu.real Bfull ≤ mu.real (Afull ∩ Bfull) := by
    simpa only [c, mu, Afull, Bfull] using
      P.freeBufferedFinite_inner_mul_exteriorCylinder_le
        N hp hp1 hq hA F S hF
  have hBdiff : |mu.real Bfull - mu.real s| < delta := by
    have hle' := abs_measureReal_sub_le_measureReal_symmDiff (μ := mu)
      hBfull.nullMeasurableSet hsfull.nullMeasurableSet
    rw [symmDiff_comm] at hle'
    exact hle'.trans_lt happReal
  have hinterSubset : (Afull ∩ Bfull) ∆ (Afull ∩ s) ⊆ s ∆ Bfull := by
    intro omega homega
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at homega ⊢
    tauto
  have hIdiff : |mu.real (Afull ∩ Bfull) - mu.real (Afull ∩ s)| < delta := by
    have habs := abs_measureReal_sub_le_measureReal_symmDiff (μ := mu)
      (hAfull.inter hBfull).nullMeasurableSet
      (hAfull.inter hsfull).nullMeasurableSet
    have hmono : mu.real ((Afull ∩ Bfull) ∆ (Afull ∩ s)) ≤
        mu.real (s ∆ Bfull) := measureReal_mono hinterSubset (by finiteness)
    exact habs.trans_lt (hmono.trans_lt happReal)
  obtain ⟨hBlow, hBup⟩ := abs_lt.mp hBdiff
  obtain ⟨hIlow, hIup⟩ := abs_lt.mp hIdiff
  dsimp [delta] at hBlow hBup hIlow hIup
  nlinarith



theorem PeriodicGraph.freeBufferedInfiniteVolume_tail_clopen_product_le
    (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A s : Set (ConfigSpace (Sym2 V))}
    (hAclopen : IsClopen A) (hAinc : IsIncreasing A)
    (hs : P.IsBufferedTailEvent s) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real A *
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (A ∩ s) := by
  obtain ⟨K, T, hAT, hTinc⟩ := P.isClopen_eq_bufferedCylinder A hAclopen
  have hT : IsIncreasing T := hTinc hAinc
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have hbound : ∀ N, K ≤ N →
      (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real A *
        mu.real s ≤ mu.real (A ∩ s) := by
    intro N hKN
    let TN : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
      P.bufferedRestrictLE hKN ⁻¹' T
    have hTN : IsIncreasing TN := fun omega eta home hmem =>
      hT (P.monotone_bufferedRestrictLE hKN home) hmem
    have hevent : P.bufferedCylinder N TN = A := by
      rw [hAT]
      ext omega
      simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage, TN]
      have hrestrict : P.bufferedRestrictLE hKN (P.bufferedRestrict N omega) =
          P.bufferedRestrict K omega := by
        funext e
        exact congrArg omega (P.edgeIncl_bufferedVertexInclLE hKN e)
      rw [hrestrict]
    simpa only [hevent] using
      P.freeBufferedFinite_inner_mul_exterior_le N hp hp1 hq hTN (hs N)
  have hconv := P.freeBufferedMeasure_tendsto_cylinder K hp hp1 hq hT
  rw [← hAT] at hconv
  have hprod : Tendsto (fun N =>
      (P.freeBufferedMeasure N hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real A * mu.real s) atTop
      (nhds (mu.real A * mu.real s)) := hconv.mul_const (mu.real s)
  exact le_of_tendsto hprod
    (Filter.eventually_atTop.mpr ⟨K, fun N hKN => hbound N hKN⟩)



theorem PeriodicGraph.freeBufferedInfiniteVolume_le_cond_tail_clopen
    (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {s : Set (ConfigSpace (Sym2 V))}
    (hs : P.IsBufferedTailEvent s)
    (hs0 : (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
    Ising.StochasticallyDominatedClopen
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      (((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _))[|s]) := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  intro A hAclopen hAinc
  have hprod := P.freeBufferedInfiniteVolume_tail_clopen_product_le
    hp hp1 hq hAclopen hAinc hs
  have hs_top : mu s ≠ ⊤ := measure_ne_top mu s
  have hs_pos : 0 < mu.real s := by
    unfold Measure.real
    exact ENNReal.toReal_pos hs0 hs_top
  have hcondReal : (mu[|s]).real A =
      (mu s).toReal⁻¹ * mu.real (A ∩ s) := by
    rw [ProbabilityTheory.cond]
    unfold Measure.real
    rw [Measure.smul_apply, Measure.restrict_apply hAclopen.isOpen.measurableSet,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change mu.real A ≤ (mu[|s]).real A
  rw [hcondReal]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hs_pos).mpr hprod


theorem PeriodicGraph.freeBufferedInfiniteVolume_tail_trivial
    (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Set (ConfigSpace (Sym2 V)))
    (hs : P.IsBufferedTailEvent s) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  by_cases hs0 : mu s = 0
  · exact Or.inl (by simpa only [mu] using hs0)
  by_cases hsc0 : mu sᶜ = 0
  · right
    have hadd := measure_add_measure_compl (μ := mu) hs.measurableSet
    rw [hsc0, add_zero] at hadd
    rw [measure_univ] at hadd
    simpa only [mu] using hadd
  haveI hp1s : IsProbabilityMeasure (mu[|s]) := cond_isProbabilityMeasure hs0
  haveI hp2s : IsProbabilityMeasure (mu[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hdom1 := P.freeBufferedInfiniteVolume_le_cond_tail_clopen
    hp hp1 hq hs hs0
  have hdom2 := P.freeBufferedInfiniteVolume_le_cond_tail_clopen
    hp hp1 hq hs.compl hsc0
  have hsum : mu s + mu sᶜ = 1 := by
    rw [← measure_univ (μ := mu)]
    exact measure_add_measure_compl hs.measurableSet
  have hdecomp : mu = mu s • (mu[|s]) + mu sᶜ • (mu[|sᶜ]) :=
    fec_invariant_decomp hs.measurableSet hs0 hsc0
  have htop : mu s ≠ ⊤ := measure_ne_top mu s
  have hsctop : mu sᶜ ≠ ⊤ := measure_ne_top mu sᶜ
  have heq := Ising.gec_min_extreme (E := Sym2 V)
    (μ := mu) (ν₁ := mu[|s]) (ν₂ := mu[|sᶜ])
    (pos_iff_ne_zero.mpr hs0) (pos_iff_ne_zero.mpr hsc0)
    hsum htop hsctop hdecomp (by simpa only [mu] using hdom1)
      (by simpa only [mu] using hdom2)
  right
  have hself : (mu[|s]) s = 1 := cond_apply_self hs0 htop
  rw [heq.1] at hself
  simpa only [mu] using hself


def PeriodicGraph.IsErgodic (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) : Prop :=
  P.IsTranslationInvariant mu ∧
    ∀ s : Set (ConfigSpace (Sym2 V)), MeasurableSet s →
      (∀ z : Site 2, P.configTranslate z ⁻¹' s = s) →
        mu s = 0 ∨ mu s = 1

omit [Countable V] in
theorem PeriodicGraph.bufferedEdgeWindow_endpoint
    (P : PeriodicGraph V) {N : ℕ} {e : Sym2 V}
    (he : e ∈ P.bufferedEdgeWindow N) {x : V} (hx : x ∈ e) :
    x ∈ P.orbitBox (P.bufferedRadius N) := by
  obtain ⟨eN, rfl⟩ := he
  induction eN using Sym2.inductionOn with
  | _ u v =>
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact u.2
      · exact v.2

omit [Countable V] in
theorem PeriodicGraph.mem_edgeVertexFinset_of_mem
    (P : PeriodicGraph V) {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ F) {x : V} (hx : x ∈ e) :
    x ∈ PeriodicGraph.edgeVertexFinset F := by
  rw [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
  exact ⟨e, he, by simpa using hx⟩

private theorem exists_finset_abs_bound
    (S : Finset V) (f : V → ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ S, |f x| ≤ R := by
  classical
  refine ⟨∑ x ∈ S, |f x|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x hx
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y)) hx



theorem PeriodicPlaneEmbedding.bufferedEdgeWindow_escape
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (F : Finset (Sym2 V)) (k : ℕ) :
    letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
      ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
    ∃ g : Multiplicative (Site 2),
      (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 V)) ⊆
        (P.bufferedEdgeWindow k)ᶜ := by
  classical
  letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
    ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
  let VF := PeriodicGraph.edgeVertexFinset F
  let VK := P.orbitBox (P.bufferedRadius k)
  obtain ⟨RF, hRF0, hRF⟩ :=
    exists_finset_abs_bound VF (fun x => E.vertexCoord x 0)
  obtain ⟨RK, hRK0, hRK⟩ :=
    exists_finset_abs_bound VK (fun x => E.vertexCoord x 0)
  obtain ⟨L : ℕ, hL⟩ := exists_nat_gt (RF + RK)
  let z : Site 2 := fun i => if i = 0 then (L : ℤ) else 0
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd z
  refine ⟨g, ?_⟩
  intro e he
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rw [Set.mem_compl_iff]
  intro hwindow
  induction e0 using Sym2.inductionOn with
  | _ x y =>
      have hxVF : x ∈ VF :=
        P.mem_edgeVertexFinset_of_mem he0 (Sym2.mem_mk_left x y)
      have hxBound : E.vertexCoord x 0 ≤ RF :=
        (le_abs_self _).trans (hRF x hxVF)
      have hxShiftMem : P.shift (-z) x ∈
          P.orbitBox (P.bufferedRadius k) := by
        apply P.bufferedEdgeWindow_endpoint hwindow
        change P.shift (-z) x ∈
          Sym2.map (P.shift (Multiplicative.toAdd g⁻¹)) s(x, y)
        have hginv : Multiplicative.toAdd g⁻¹ = -z := rfl
        rw [hginv, Sym2.map_mk]
        exact Sym2.mem_mk_left _ _
      have hxTarget : -RK ≤ E.vertexCoord (P.shift (-z) x) 0 := by
        have habs := hRK (P.shift (-z) x) hxShiftMem
        exact (neg_le_of_abs_le habs)
      have hz0 : z 0 = (L : ℤ) := by simp [z]
      have hcoord : E.vertexCoord (P.shift (-z) x) 0 =
          E.vertexCoord x 0 - L := by
        rw [E.vertexCoord_shift]
        simp [hz0]
        ring
      rw [hcoord] at hxTarget
      have hLreal : RF + RK < (L : ℝ) := by exact_mod_cast hL
      linarith



theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_isErgodic
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    P.IsErgodic
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have hTI := P.freeBufferedInfiniteVolume_isTranslationInvariant hp hp1 hq
  refine ⟨hTI, ?_⟩
  intro s hs hinv
  letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
    ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
  letI : SemigroupAction (Multiplicative (Site 2)) (Sym2 V) := ⟨by
    intro g h e
    change Sym2.map (P.shift (g * h).toAdd) e =
      Sym2.map (P.shift g.toAdd) (Sym2.map (P.shift h.toAdd) e)
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [Sym2.map_mk]
        rw [show (g * h).toAdd = g.toAdd + h.toAdd from rfl]
        congr 1
        · exact (by simpa [add_comm] using P.shift_add h.toAdd g.toAdd x)
        · exact (by simpa [add_comm] using P.shift_add h.toAdd g.toAdd y)
    ⟩
  letI : MulAction (Multiplicative (Site 2)) (Sym2 V) := ⟨by
    intro e
    change Sym2.map (P.shift (1 : Multiplicative (Site 2)).toAdd) e = e
    induction e using Sym2.inductionOn with
    | _ x y => simp [P.shift_zero]
    ⟩
  have htranslate (z : Site 2) :
      P.configTranslate z = ConfigSpace.shift (Multiplicative.ofAdd z) := by
    funext omega e
    induction e using Sym2.inductionOn with
    | _ x y => rfl
  have hTIstd : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    intro g
    have ht := htranslate g.toAdd
    change P.configTranslate g.toAdd = ConfigSpace.shift g at ht
    rw [← ht]
    exact hTI g.toAdd
  have hinvStd : ∀ g : Multiplicative (Site 2),
      ConfigSpace.shift g ⁻¹' s = s := by
    intro g
    have ht := htranslate g.toAdd
    change P.configTranslate g.toAdd = ConfigSpace.shift g at ht
    rw [← ht]
    exact hinv g.toAdd
  have hescape : ∀ (F : Finset (Sym2 V)) (k : ℕ),
      ∃ g : Multiplicative (Site 2),
        (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 V)) ⊆
          (P.bufferedEdgeWindow k)ᶜ := by
    intro F k
    exact E.bufferedEdgeWindow_escape F k
  obtain ⟨t, ht, hae⟩ := ati_invariant_aeTail P.bufferedEdgeWindow
    P.bufferedEdgeWindow_mono hescape hTIstd s hs hinvStd
  have heq : mu s = mu t := measure_congr hae
  rcases P.freeBufferedInfiniteVolume_tail_trivial hp hp1 hq t ht with ht0 | ht1
  · exact Or.inl (heq.trans ht0)
  · exact Or.inr (heq.trans ht1)

end PeriodicPlanar
end FK
end StatMech
