/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Sharpness.HighTempSwitching

open Finset SimpleGraph
open scoped BigOperators symmDiff

namespace StatMech
namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def highTempInternalEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (edgeInside S)

@[simp] theorem mem_highTempInternalEdges (S : Finset V) (e : Sym2 V) :
    e ∈ highTempInternalEdges G S ↔
      e ∈ G.edgeFinset ∧ edgeInside S e := by
  simp [highTempInternalEdges]


structure HighTempSwitchInput where
  F : Finset (Sym2 V)
  H : Finset (Sym2 V)
deriving DecidableEq, Fintype


structure HighTempSwitchOutput where
  x : V
  y : V
  A : Finset (Sym2 V)
  B : Finset (Sym2 V)
deriving DecidableEq, Fintype



def HighTempSwitchInput.Valid (S : Finset V) (o z : V)
    (p : HighTempSwitchInput (V := V)) : Prop :=
  p.F ⊆ G.edgeFinset ∧
    p.H ⊆ highTempInternalEdges G S ∧
    HasOddBoundary p.F (sourcePair o z) ∧
    HasOddBoundary p.H ∅

noncomputable instance (S : Finset V) (o z : V) :
    DecidablePred (HighTempSwitchInput.Valid G S o z) :=
  fun _ => Classical.propDecidable _


def HighTempSwitchOutput.Valid (S : Finset V) (o z : V)
    (r : HighTempSwitchOutput (V := V)) : Prop :=
  r.x ∈ S ∧ r.y ∉ S ∧
    r.A ⊆ highTempInternalEdges G S ∧
    r.B ⊆ G.edgeFinset ∧
    HasOddBoundary r.A (sourcePair o r.x) ∧
    HasOddBoundary r.B (sourcePair r.y z)

noncomputable instance (S : Finset V) (o z : V) :
    DecidablePred (HighTempSwitchOutput.Valid G S o z) :=
  fun _ => Classical.propDecidable _

noncomputable def highTempSwitchInputs (S : Finset V) (o z : V) :
    Finset (HighTempSwitchInput (V := V)) :=
  Finset.univ.filter (HighTempSwitchInput.Valid G S o z)

noncomputable def highTempSwitchOutputs (S : Finset V) (o z : V) :
    Finset (HighTempSwitchOutput (V := V)) :=
  Finset.univ.filter (HighTempSwitchOutput.Valid G S o z)


theorem highTempInput_symmDiff_subset {S : Finset V} {o z : V}
    {p : HighTempSwitchInput (V := V)} (hp : p.Valid G S o z) :
    p.F ∆ p.H ⊆ G.edgeFinset := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨heF, _⟩ | ⟨heH, _⟩
  · exact hp.1 heF
  · exact (mem_highTempInternalEdges G S e).mp (hp.2.1 heH) |>.1


theorem highTempInput_symmDiff_sources {S : Finset V} {o z : V}
    {p : HighTempSwitchInput (V := V)} (hp : p.Valid G S o z) :
    HasOddBoundary (p.F ∆ p.H) (sourcePair o z) := by
  have h := hasOddBoundary_symmDiff hp.2.2.1 hp.2.2.2
  convert h using 1
  ext v
  simp only [Finset.mem_symmDiff, Finset.notMem_empty,
    not_false_eq_true, and_true, false_and, or_false]


noncomputable def highTempSwitch (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) (p : HighTempSwitchInput (V := V))
    (hp : p.Valid G S o z) : HighTempSwitchOutput (V := V) := by
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hp)
    (highTempInput_symmDiff_sources G hp) S ho hz
  exact
    { x := d.x
      y := d.y
      A := p.H ∆ d.Q
      B := (p.F ∆ d.Q).erase s(d.x, d.y) }

theorem highTempSwitch_mem_outputs (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) (p : HighTempSwitchInput (V := V))
    (hp : p ∈ highTempSwitchInputs G S o z) :
    highTempSwitch G S o z ho hz p (by simpa [highTempSwitchInputs] using hp)
      ∈ highTempSwitchOutputs G S o z := by
  classical
  have hpv : p.Valid G S o z := by
    simpa [highTempSwitchInputs] using hp
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hpv)
    (highTempInput_symmDiff_sources G hpv) S ho hz
  have hQG : d.Q ⊆ G.edgeFinset := d.Q_subset.trans
    (highTempInput_symmDiff_subset G hpv)
  have hQI : d.Q ⊆ highTempInternalEdges G S := by
    intro e he
    exact (mem_highTempInternalEdges G S e).2 ⟨hQG he, d.Q_inside e he⟩
  have hAsub : p.H ∆ d.Q ⊆ highTempInternalEdges G S := by
    intro e he
    rw [Finset.mem_symmDiff] at he
    exact he.elim (fun h => hpv.2.1 h.1) (fun h => hQI h.1)
  have hBsub : (p.F ∆ d.Q).erase s(d.x, d.y) ⊆ G.edgeFinset := by
    intro e he
    have he' := Finset.mem_of_mem_erase he
    rw [Finset.mem_symmDiff] at he'
    exact he'.elim (fun h => hpv.1 h.1) (fun h => hQG h.1)
  have hexitF : s(d.x, d.y) ∈ p.F := by
    have heK := d.exit_mem
    change s(d.x, d.y) ∈ p.F ∆ p.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hpv.2.1 h.1) |>.2
      exact d.y_notMem (hinside d.y (Sym2.mem_mk_right d.x d.y))
  have hsources := hasOddBoundary_switch_erase_exit
    hpv.2.2.1 hpv.2.2.2 d.Q_sources d.ne hexitF d.exit_notMem
  rw [highTempSwitchOutputs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  change HighTempSwitchOutput.Valid G S o z
    (highTempSwitch G S o z ho hz p _) at ⊢
  simpa only [highTempSwitch, K, d] using
    ⟨d.x_mem, d.y_notMem, hAsub, hBsub, hsources.1, hsources.2⟩





theorem highTempSwitch_recover_symmDiff
    (F H Q : Finset (Sym2 V)) {e : Sym2 V}
    (heF : e ∈ F) (heQ : e ∉ Q) :
    insert e ((F ∆ Q).erase e) ∆ (H ∆ Q) = F ∆ H := by
  have he : e ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  rw [Finset.insert_erase he]
  ext a
  simp only [Finset.mem_symmDiff]
  tauto



theorem highTempSwitch_recover_F
    (F Q : Finset (Sym2 V)) {e : Sym2 V}
    (heF : e ∈ F) (heQ : e ∉ Q) :
    insert e ((F ∆ Q).erase e) ∆ Q = F := by
  have he : e ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  rw [Finset.insert_erase he]
  ext a
  simp only [Finset.mem_symmDiff]
  tauto



theorem highTempSwitch_recover_H (H Q : Finset (Sym2 V)) :
    (H ∆ Q) ∆ Q = H := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


noncomputable def highTempSwitchMap (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) :
    ↥(highTempSwitchInputs G S o z) → ↥(highTempSwitchOutputs G S o z) :=
  fun p => ⟨highTempSwitch G S o z ho hz p.1 (by
      have h := p.2
      change p.1 ∈ Finset.univ.filter
        (HighTempSwitchInput.Valid G S o z) at h
      exact (Finset.mem_filter.mp h).2),
    highTempSwitch_mem_outputs G S o z ho hz p.1 p.2⟩




theorem highTempSwitchMap_injective (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) :
    Function.Injective (highTempSwitchMap G S o z ho hz) := by
  classical
  intro p q hpq
  have hpv : p.1.Valid G S o z := by
    have h := p.2
    change p.1 ∈ Finset.univ.filter
      (HighTempSwitchInput.Valid G S o z) at h
    exact (Finset.mem_filter.mp h).2
  have hqv : q.1.Valid G S o z := by
    have h := q.2
    change q.1 ∈ Finset.univ.filter
      (HighTempSwitchInput.Valid G S o z) at h
    exact (Finset.mem_filter.mp h).2
  let dp := highTempFirstExit G (p.1.F ∆ p.1.H)
    (highTempInput_symmDiff_subset G hpv)
    (highTempInput_symmDiff_sources G hpv) S ho hz
  let dq := highTempFirstExit G (q.1.F ∆ q.1.H)
    (highTempInput_symmDiff_subset G hqv)
    (highTempInput_symmDiff_sources G hqv) S ho hz
  have hout :
      highTempSwitch G S o z ho hz p.1 hpv =
        highTempSwitch G S o z ho hz q.1 hqv := by
    exact Subtype.ext_iff.mp hpq
  have hx : dp.x = dq.x := by
    have := congrArg HighTempSwitchOutput.x hout
    simpa only [highTempSwitch, dp, dq] using this
  have hy : dp.y = dq.y := by
    have := congrArg HighTempSwitchOutput.y hout
    simpa only [highTempSwitch, dp, dq] using this
  have hA : p.1.H ∆ dp.Q = q.1.H ∆ dq.Q := by
    have := congrArg HighTempSwitchOutput.A hout
    simpa only [highTempSwitch, dp, dq] using this
  have hB : (p.1.F ∆ dp.Q).erase s(dp.x, dp.y) =
      (q.1.F ∆ dq.Q).erase s(dq.x, dq.y) := by
    have := congrArg HighTempSwitchOutput.B hout
    simpa only [highTempSwitch, dp, dq] using this
  have hB' : (p.1.F ∆ dp.Q).erase s(dq.x, dq.y) =
      (q.1.F ∆ dq.Q).erase s(dq.x, dq.y) := by
    simpa only [hx, hy] using hB
  have hexitFp : s(dp.x, dp.y) ∈ p.1.F := by
    have heK := dp.exit_mem
    change s(dp.x, dp.y) ∈ p.1.F ∆ p.1.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hpv.2.1 h.1) |>.2
      exact dp.y_notMem (hinside dp.y (Sym2.mem_mk_right dp.x dp.y))
  have hexitFq : s(dq.x, dq.y) ∈ q.1.F := by
    have heK := dq.exit_mem
    change s(dq.x, dq.y) ∈ q.1.F ∆ q.1.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hqv.2.1 h.1) |>.2
      exact dq.y_notMem (hinside dq.y (Sym2.mem_mk_right dq.x dq.y))
  have hK : p.1.F ∆ p.1.H = q.1.F ∆ q.1.H := by
    rw [← highTempSwitch_recover_symmDiff p.1.F p.1.H dp.Q
        hexitFp dp.exit_notMem,
      ← highTempSwitch_recover_symmDiff q.1.F q.1.H dq.Q
        hexitFq dq.exit_notMem]
    rw [hx, hy, hA, hB']
  have hQ : dp.Q = dq.Q := by
    exact highTempFirstExit_Q_congr G hK
      (highTempInput_symmDiff_subset G hpv)
      (highTempInput_symmDiff_subset G hqv)
      (highTempInput_symmDiff_sources G hpv)
      (highTempInput_symmDiff_sources G hqv) S ho hz
  have hH : p.1.H = q.1.H := by
    calc
      p.1.H = (p.1.H ∆ dp.Q) ∆ dp.Q :=
        (highTempSwitch_recover_H p.1.H dp.Q).symm
      _ = (q.1.H ∆ dq.Q) ∆ dq.Q := by rw [hA, hQ]
      _ = q.1.H := highTempSwitch_recover_H q.1.H dq.Q
  have hF : p.1.F = q.1.F := by
    calc
      p.1.F = insert s(dp.x, dp.y)
          ((p.1.F ∆ dp.Q).erase s(dp.x, dp.y)) ∆ dp.Q :=
        (highTempSwitch_recover_F p.1.F dp.Q hexitFp dp.exit_notMem).symm
      _ = insert s(dq.x, dq.y)
          ((q.1.F ∆ dq.Q).erase s(dq.x, dq.y)) ∆ dq.Q := by
        rw [hx, hy, hB', hQ]
      _ = q.1.F :=
        highTempSwitch_recover_F q.1.F dq.Q hexitFq dq.exit_notMem
  apply Subtype.ext
  exact congrArg₂ (fun F H => HighTempSwitchInput.mk F H) hF hH



noncomputable def highTempSwitchInputWeight (t : Sym2 V → ℝ)
    (p : HighTempSwitchInput (V := V)) : ℝ :=
  (∏ e ∈ p.F, t e) * ∏ e ∈ p.H, t e

noncomputable def highTempSwitchOutputWeight (t : Sym2 V → ℝ)
    (r : HighTempSwitchOutput (V := V)) : ℝ :=
  (∏ e ∈ r.A, t e) * t s(r.x, r.y) * ∏ e ∈ r.B, t e


theorem highTempSwitch_weight_eq (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S)
    (p : HighTempSwitchInput (V := V)) (hp : p.Valid G S o z) :
    highTempSwitchOutputWeight t (highTempSwitch G S o z ho hz p hp) =
      highTempSwitchInputWeight t p := by
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hp)
    (highTempInput_symmDiff_sources G hp) S ho hz
  have hexitF : s(d.x, d.y) ∈ p.F := by
    have heK := d.exit_mem
    change s(d.x, d.y) ∈ p.F ∆ p.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hp.2.1 h.1) |>.2
      exact d.y_notMem (hinside d.y (Sym2.mem_mk_right d.x d.y))
  simpa only [highTempSwitchOutputWeight, highTempSwitchInputWeight,
    highTempSwitch, K, d] using
    prod_switch_erase_exit t p.F p.H d.Q d.Q_subset hexitF d.exit_notMem



theorem highTempSwitch_sum_le (t : Sym2 V → ℝ) (ht : ∀ e, 0 ≤ t e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) ≤
      ∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1 := by
  classical
  let f := highTempSwitchMap G S o z ho hz
  have hf : Function.Injective f := highTempSwitchMap_injective G S o z ho hz
  have hweight : ∀ p : ↥(highTempSwitchInputs G S o z),
      highTempSwitchInputWeight t p.1 = highTempSwitchOutputWeight t (f p).1 := by
    intro p
    have hpv : p.1.Valid G S o z := by
      have h := p.2
      change p.1 ∈ Finset.univ.filter
        (HighTempSwitchInput.Valid G S o z) at h
      exact (Finset.mem_filter.mp h).2
    exact (highTempSwitch_weight_eq G t S o z ho hz p.1 hpv).symm
  calc
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
        ∑ p : ↥(highTempSwitchInputs G S o z),
          highTempSwitchOutputWeight t (f p).1 := by
            apply Finset.sum_congr rfl
            intro p _
            exact hweight p
    _ = ∑ r ∈ (Finset.univ.image f), highTempSwitchOutputWeight t r.1 := by
      symm
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hf hab
    _ ≤ ∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro r _ _
      unfold highTempSwitchOutputWeight
      exact mul_nonneg
        (mul_nonneg
          (Finset.prod_nonneg (fun e _ => ht e))
          (ht s(r.1.x, r.1.y)))
        (Finset.prod_nonneg (fun e _ => ht e))



noncomputable def highTempSourceSubgraphs (E : Finset (Sym2 V))
    (A : Finset V) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter (fun F => HasOddBoundary F A)

noncomputable def highTempSourceSum (E : Finset (Sym2 V))
    (t : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ∑ F ∈ highTempSourceSubgraphs E A, ∏ e ∈ F, t e

theorem highTempSwitch_input_sum (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) :
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
      highTempSourceSum G.edgeFinset t (sourcePair o z) *
        highTempSourceSum (highTempInternalEdges G S) t ∅ := by
  classical
  let SF := highTempSourceSubgraphs G.edgeFinset (sourcePair o z)
  let SH := highTempSourceSubgraphs (highTempInternalEdges G S) ∅
  have hreindex :
      (∑ p ∈ highTempSwitchInputs G S o z,
          highTempSwitchInputWeight t p) =
        ∑ q ∈ SF ×ˢ SH,
          (∏ e ∈ q.1, t e) * ∏ e ∈ q.2, t e := by
    apply Finset.sum_bij (fun p _ => (p.F, p.H))
    · intro p hp
      rw [highTempSwitchInputs, Finset.mem_filter] at hp
      rw [Finset.mem_product]
      constructor
      · have hmem : p.F ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair o z) := by
          rw [highTempSourceSubgraphs, Finset.mem_filter,
            Finset.mem_powerset]
          exact ⟨hp.2.1, hp.2.2.2.1⟩
        simpa only [SF] using hmem
      · have hmem : p.H ∈ highTempSourceSubgraphs
            (highTempInternalEdges G S) ∅ := by
          rw [highTempSourceSubgraphs, Finset.mem_filter,
            Finset.mem_powerset]
          exact ⟨hp.2.2.1, hp.2.2.2.2⟩
        simpa only [SH] using hmem
    · intro p hp q hq heq
      cases p
      cases q
      simp_all
    · intro q hq
      rw [Finset.mem_product] at hq
      have hF := hq.1
      have hH := hq.2
      dsimp only [SF] at hF
      dsimp only [SH] at hH
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hF hH
      let p : HighTempSwitchInput (V := V) := ⟨q.1, q.2⟩
      refine ⟨p, ?_, rfl⟩
      rw [highTempSwitchInputs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hF.1, hH.1, hF.2, hH.2⟩
    · intro p hp
      rfl
  calc
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
        ∑ p ∈ highTempSwitchInputs G S o z,
          highTempSwitchInputWeight t p := by
            simpa only [Finset.attach_eq_univ] using
              Finset.sum_attach (highTempSwitchInputs G S o z)
                (highTempSwitchInputWeight t)
    _ = ∑ q ∈ SF ×ˢ SH,
          (∏ e ∈ q.1, t e) * ∏ e ∈ q.2, t e := hreindex
    _ = (∑ F ∈ SF, ∏ e ∈ F, t e) *
          ∑ H ∈ SH, ∏ e ∈ H, t e := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
    _ = _ := by rfl

set_option maxHeartbeats 2000000 in

theorem highTempSwitch_output_sum (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) :
    (∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1) =
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t
            (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
  classical
  let T : Finset (V × V × Finset (Sym2 V) × Finset (Sym2 V)) :=
    Finset.univ.filter (fun q =>
      q.1 ∈ S ∧ q.2.1 ∉ S ∧
        q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
          (sourcePair o q.1) ∧
        q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
          (sourcePair q.2.1 z))
  have hreindex :
      (∑ r ∈ highTempSwitchOutputs G S o z,
          highTempSwitchOutputWeight t r) =
        ∑ q ∈ T,
          (∏ e ∈ q.2.2.1, t e) * t s(q.1, q.2.1) *
            ∏ e ∈ q.2.2.2, t e := by
    apply Finset.sum_bij (fun r _ => (r.x, r.y, r.A, r.B))
    · intro r hr
      rw [highTempSwitchOutputs, Finset.mem_filter] at hr
      change (r.x, r.y, r.A, r.B) ∈ Finset.univ.filter (fun q =>
        q.1 ∈ S ∧ q.2.1 ∉ S ∧
          q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
            (sourcePair o q.1) ∧
          q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair q.2.1 z))
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hr.2.1, hr.2.2.1, ?_, ?_⟩
      · rw [highTempSourceSubgraphs, Finset.mem_filter,
          Finset.mem_powerset]
        exact ⟨hr.2.2.2.1, hr.2.2.2.2.2.1⟩
      · rw [highTempSourceSubgraphs, Finset.mem_filter,
          Finset.mem_powerset]
        exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.2⟩
    · intro r hr u hu heq
      cases r
      cases u
      simp_all
    · intro q hq
      change q ∈ Finset.univ.filter (fun q =>
        q.1 ∈ S ∧ q.2.1 ∉ S ∧
          q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
            (sourcePair o q.1) ∧
          q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair q.2.1 z)) at hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨_, hx, hy, hA, hB⟩
      let r : HighTempSwitchOutput (V := V) :=
        ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
      refine ⟨r, ?_, rfl⟩
      rw [highTempSwitchOutputs, Finset.mem_filter]
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hA hB
      exact ⟨Finset.mem_univ _, hx, hy,
        hA.1, hB.1, hA.2, hB.2⟩
    · intro r hr
      rfl
  rw [show (∑ r : ↥(highTempSwitchOutputs G S o z),
      highTempSwitchOutputWeight t r.1) =
      ∑ r ∈ highTempSwitchOutputs G S o z,
        highTempSwitchOutputWeight t r by
      simpa only [Finset.attach_eq_univ] using
        Finset.sum_attach (highTempSwitchOutputs G S o z)
          (highTempSwitchOutputWeight t)]
  rw [hreindex]
  unfold T
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  have hsum_mem (f : V → ℝ) :
      (∑ x ∈ S, f x) = ∑ x : V, if x ∈ S then f x else 0 := by
    have hs : S = Finset.univ.filter (fun x => x ∈ S) := by
      ext x
      simp
    calc
      (∑ x ∈ S, f x) =
          ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), f x := by
            exact Finset.sum_congr hs (fun _ _ => rfl)
      _ = _ := Finset.sum_filter (s := (Finset.univ : Finset V))
        (p := fun x => x ∈ S) f
  have hsum_notMem (f : V → ℝ) :
      (∑ y ∈ Finset.univ \ S, f y) =
        ∑ y : V, if y ∉ S then f y else 0 := by
    calc
      (∑ y ∈ Finset.univ \ S, f y) =
          ∑ y ∈ Finset.univ.filter (fun y => y ∉ S), f y := by
            apply Finset.sum_congr
            · ext y
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
                Finset.mem_filter]
            · intros
              rfl
      _ = _ := Finset.sum_filter (s := (Finset.univ : Finset V))
        (p := fun y => y ∉ S) f
  have hsum_family (U : Finset (Finset (Sym2 V)))
      (f : Finset (Sym2 V) → ℝ) :
      (∑ A : Finset (Sym2 V), if A ∈ U then f A else 0) =
        ∑ A ∈ U, f A := by
    symm
    have hU : U = Finset.univ.filter (fun A => A ∈ U) := by
      ext A
      simp
    calc
      (∑ A ∈ U, f A) =
          ∑ A ∈ Finset.univ.filter (fun A => A ∈ U), f A := by
            exact Finset.sum_congr hU (fun _ _ => rfl)
      _ = _ := Finset.sum_filter (s := (Finset.univ :
        Finset (Finset (Sym2 V)))) (p := fun A => A ∈ U) f
  rw [hsum_mem]
  simp_rw [hsum_notMem]
  simp only [highTempSourceSum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ S
  · rw [if_pos hx]
    rw [Finset.sum_congr rfl]
    intro y _
    by_cases hy : y ∉ S
    · rw [if_pos hy]
      simp only [hx, hy, not_false_eq_true, true_and]
      let SA := highTempSourceSubgraphs (highTempInternalEdges G S)
        (sourcePair o x)
      let SB := highTempSourceSubgraphs G.edgeFinset (sourcePair y z)
      calc
        (∑ A : Finset (Sym2 V), ∑ B : Finset (Sym2 V),
            if A ∈ SA ∧ B ∈ SB then
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e else 0) =
          ∑ A : Finset (Sym2 V), if A ∈ SA then
            (∑ B : Finset (Sym2 V), if B ∈ SB then
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e else 0) else 0 := by
                apply Finset.sum_congr rfl
                intro A _
                by_cases hA : A ∈ SA
                · rw [if_pos hA]
                  apply Finset.sum_congr rfl
                  intro B _
                  by_cases hB : B ∈ SB <;> simp [hA, hB]
                · rw [if_neg hA]
                  simp only [hA, false_and, if_false,
                    Finset.sum_const_zero]
        _ = ∑ A ∈ SA, ∑ B ∈ SB,
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e := by
                rw [hsum_family]
                apply Finset.sum_congr rfl
                intro A _
                rw [hsum_family]
        _ = (t s(x, y) * ∑ A ∈ SA, ∏ e ∈ A, t e) *
              ∑ B ∈ SB, ∏ e ∈ B, t e := by
                let WB := ∑ B ∈ SB, ∏ e ∈ B, t e
                calc
                  (∑ A ∈ SA, ∑ B ∈ SB,
                      (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e) =
                    ∑ A ∈ SA, ((∏ e ∈ A, t e) * t s(x, y)) * WB := by
                      apply Finset.sum_congr rfl
                      intro A _
                      unfold WB
                      rw [Finset.mul_sum]
                  _ = (∑ A ∈ SA, (∏ e ∈ A, t e) * t s(x, y)) * WB := by
                      rw [Finset.sum_mul]
                  _ = _ := by
                      rw [← Finset.sum_mul]
                      ring
    · simp [hx, hy]
  · simp [hx]


theorem highTemp_sourceSum_simon (t : Sym2 V → ℝ) (ht : ∀ e, 0 ≤ t e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    highTempSourceSum G.edgeFinset t (sourcePair o z) *
        highTempSourceSum (highTempInternalEdges G S) t ∅ ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t
            (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
  rw [← highTempSwitch_input_sum G t S o z,
    ← highTempSwitch_output_sum G t S o z]
  exact highTempSwitch_sum_le G t ht S o z ho hz





theorem highTempSourceSum_zero_extension
    (I E : Finset (Sym2 V)) (hIE : I ⊆ E)
    (t t' : Sym2 V → ℝ)
    (hin : ∀ e ∈ I, t' e = t e)
    (hout : ∀ e ∈ E, e ∉ I → t' e = 0)
    (A : Finset V) :
    highTempSourceSum E t' A = highTempSourceSum I t A := by
  classical
  have hsub : highTempSourceSubgraphs I A ⊆
      highTempSourceSubgraphs E A := by
    intro F hF
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hF ⊢
    exact ⟨hF.1.trans hIE, hF.2⟩
  have hzero : ∀ F ∈ highTempSourceSubgraphs E A,
      F ∉ highTempSourceSubgraphs I A → (∏ e ∈ F, t' e) = 0 := by
    intro F hFE hFI
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hFE
    have hnsub : ¬ F ⊆ I := by
      intro hsubI
      apply hFI
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset]
      exact ⟨hsubI, hFE.2⟩
    rw [Finset.not_subset] at hnsub
    obtain ⟨e, heF, heI⟩ := hnsub
    exact Finset.prod_eq_zero heF (hout e (hFE.1 heF) heI)
  have hext :
      (∑ F ∈ highTempSourceSubgraphs I A, ∏ e ∈ F, t' e) =
        ∑ F ∈ highTempSourceSubgraphs E A, ∏ e ∈ F, t' e :=
    Finset.sum_subset hsub hzero
  unfold highTempSourceSum
  rw [← hext]
  apply Finset.sum_congr rfl
  intro F hF
  apply Finset.prod_congr rfl
  intro e he
  have hFI : F ⊆ I := by
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hF
    exact hF.1
  exact hin e (hFI he)



theorem highTempSourceSum_couplingIn (beta : ℝ) (J : Sym2 V → ℝ)
    (S A : Finset V) :
    highTempSourceSum G.edgeFinset
        (fun e => Real.tanh (beta * couplingIn J S e)) A =
      highTempSourceSum (highTempInternalEdges G S)
        (fun e => Real.tanh (beta * J e)) A := by
  apply highTempSourceSum_zero_extension
    (highTempInternalEdges G S) G.edgeFinset
  · intro e he
    exact (mem_highTempInternalEdges G S e).mp he |>.1
  · intro e he
    have hins := (mem_highTempInternalEdges G S e).mp he |>.2
    simp [couplingIn, hins]
  · intro e heG heI
    have hninside : ¬ edgeInside S e := by
      intro h
      exact heI ((mem_highTempInternalEdges G S e).2 ⟨heG, h⟩)
    simp [couplingIn, hninside]


noncomputable def twoPointJ (beta : ℝ) (J : Sym2 V → ℝ)
    (a b : V) : ℝ :=
  expectationJ G beta J (sourcePair a b)

@[simp] theorem twoPointJ_self (beta : ℝ) (J : Sym2 V → ℝ) (a : V) :
    twoPointJ G beta J a a = 1 := by
  rw [twoPointJ, sourcePair_self]
  unfold expectationJ partitionJ
  simp only [spinProd_empty, one_mul]
  exact div_self (ne_of_gt (partitionJ_pos G beta J))


theorem twoPointJ_high_temp_ratio (beta : ℝ) (J : Sym2 V → ℝ)
    (a b : V) :
    twoPointJ G beta J a b =
      highTempSourceSum G.edgeFinset
          (fun e => Real.tanh (beta * J e)) (sourcePair a b) /
        highTempSourceSum G.edgeFinset
          (fun e => Real.tanh (beta * J e)) ∅ := by
  unfold twoPointJ
  rw [expectationJ_high_temp_ratio]
  unfold highTempSourceSum highTempSourceSubgraphs
  simp only [highTempSubgraphWeight]
  apply congrArg₂ (· / ·)
  · rfl
  · apply Finset.sum_congr
    · ext F
      simp only [Finset.mem_filter, hasOddBoundary_empty]
    · intro F _
      rfl



theorem highTempSourceSum_empty_pos (E : Finset (Sym2 V))
    (t : Sym2 V → ℝ) (ht : ∀ e ∈ E, 0 ≤ t e) :
    0 < highTempSourceSum E t ∅ := by
  unfold highTempSourceSum highTempSourceSubgraphs
  have hempty : (∅ : Finset (Sym2 V)) ∈
      E.powerset.filter (fun F => HasOddBoundary F ∅) := by
    rw [Finset.mem_filter, Finset.mem_powerset, hasOddBoundary_empty]
    exact ⟨Finset.empty_subset _, by
      intro v
      simp [incCount]⟩
  calc
    0 < (1 : ℝ) := zero_lt_one
    _ = ∏ e ∈ (∅ : Finset (Sym2 V)), t e := by simp
    _ ≤ ∑ F ∈ E.powerset.filter (fun F => HasOddBoundary F ∅),
          ∏ e ∈ F, t e := by
      rw [← Finset.add_sum_erase _ _ hempty]
      simp only [Finset.prod_empty]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun F hF =>
        Finset.prod_nonneg (fun e he => by
          have hmem := Finset.mem_of_mem_erase hF
          have hpow := (Finset.mem_filter.mp hmem).1
          exact ht e ((Finset.mem_powerset.mp hpow) he))))


theorem twoPointJ_couplingIn_high_temp_ratio (beta : ℝ)
    (J : Sym2 V → ℝ) (S : Finset V) (a b : V) :
    twoPointJ G beta (couplingIn J S) a b =
      highTempSourceSum (highTempInternalEdges G S)
          (fun e => Real.tanh (beta * J e)) (sourcePair a b) /
        highTempSourceSum (highTempInternalEdges G S)
          (fun e => Real.tanh (beta * J e)) ∅ := by
  rw [twoPointJ_high_temp_ratio]
  rw [highTempSourceSum_couplingIn G beta J S (sourcePair a b),
    highTempSourceSum_couplingIn G beta J S ∅]




theorem twoPointJ_simon_finite (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    twoPointJ G beta J o z ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        Real.tanh (beta * J s(x, y)) *
          twoPointJ G beta (couplingIn J S) o x *
          twoPointJ G beta J y z := by
  let t : Sym2 V → ℝ := fun e => Real.tanh (beta * J e)
  have ht : ∀ e, 0 ≤ t e := by
    intro e
    change 0 ≤ Real.tanh (beta * J e)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ e)))
      (Real.cosh_pos _).le
  let ZG := highTempSourceSum G.edgeFinset t ∅
  let ZS := highTempSourceSum (highTempInternalEdges G S) t ∅
  let N := highTempSourceSum G.edgeFinset t (sourcePair o z)
  let R := ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
    t s(x, y) *
      (highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) / ZS) *
      highTempSourceSum G.edgeFinset t (sourcePair y z)
  have hZG : 0 < ZG := highTempSourceSum_empty_pos G.edgeFinset t
    (fun e _ => ht e)
  have hZS : 0 < ZS := highTempSourceSum_empty_pos
    (highTempInternalEdges G S) t (fun e _ => ht e)
  have hcross : N * ZS ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) *
          highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
    exact highTemp_sourceSum_simon G t ht S o z ho hz
  have hNR : N ≤ R := by
    apply le_of_mul_le_mul_right _ hZS
    calc
      N * ZS ≤ ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
          t s(x, y) *
            highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) *
            highTempSourceSum G.edgeFinset t (sourcePair y z) := hcross
      _ = R * ZS := by
        unfold R
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y _
        field_simp
  have hrat : N / ZG ≤ R / ZG :=
    div_le_div_of_nonneg_right hNR hZG.le
  rw [twoPointJ_high_temp_ratio G beta J o z,
    show highTempSourceSum G.edgeFinset
      (fun e => Real.tanh (beta * J e)) (sourcePair o z) = N by rfl,
    show highTempSourceSum G.edgeFinset
      (fun e => Real.tanh (beta * J e)) ∅ = ZG by rfl]
  calc
    N / ZG ≤ R / ZG := hrat
    _ = ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        Real.tanh (beta * J s(x, y)) *
          twoPointJ G beta (couplingIn J S) o x *
          twoPointJ G beta J y z := by
      unfold R
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      rw [twoPointJ_couplingIn_high_temp_ratio,
        twoPointJ_high_temp_ratio]
      dsimp only [t, ZS, ZG]
      ring



theorem twoPointJ_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (a b : V) :
    0 ≤ twoPointJ G beta J a b := by
  let t : Sym2 V → ℝ := fun e => Real.tanh (beta * J e)
  have ht : ∀ e, 0 ≤ t e := by
    intro e
    change 0 ≤ Real.tanh (beta * J e)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ e)))
      (Real.cosh_pos _).le
  rw [twoPointJ_high_temp_ratio]
  exact div_nonneg
    (Finset.sum_nonneg (fun F _ => Finset.prod_nonneg (fun e _ => ht e)))
    (highTempSourceSum_empty_pos G.edgeFinset t (fun e _ => ht e)).le


noncomputable def simonWeightPair (beta : ℝ) (J : Sym2 V → ℝ)
    (S : Finset V) (o x y : V) : ℝ :=
  Real.tanh (beta * J s(x, y)) *
    twoPointJ G beta (couplingIn J S) o x



theorem twoPointJ_simonLieb_finite (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o : V) (ho : o ∈ S) :
    SimonLieb (twoPointJ G beta J) o S
      (simonWeightPair G beta J S o) (Finset.univ \ S) := by
  apply simonLieb_of_firstExit
  · exact fun a b => twoPointJ_nonneg G beta J hbeta hJ a b
  · intro x y
    unfold simonWeightPair
    apply mul_nonneg
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ s(x, y))))
        (Real.cosh_pos _).le
    · apply twoPointJ_nonneg G beta (couplingIn J S) hbeta
      intro e
      unfold couplingIn
      split <;> simp_all [hJ e]
  · intro z hz
    simpa only [simonWeightPair] using
      twoPointJ_simon_finite G beta J hbeta hJ S o z ho hz

end Sharpness
end StatMech
