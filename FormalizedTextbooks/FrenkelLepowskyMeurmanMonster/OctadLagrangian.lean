/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LagrangianFourier
/-! Physical isotropy for three overlapping binary octad supports.

Three even vectors are supported on o, p, and o+p. If their sum lies in
the span of o and p, their componentwise pairing with any other such triple
vanishes. Gauging the first two components makes the total sum zero, after
which each physical point cancels. The possible gauge parity correction
also vanishes by total evenness, so no word-weight assumptions are needed.
The final interface uses Fin 3 triples and actual span membership.
Source: the binary physical support calculation in Seysen's octad triality. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
-- Binary coordinate functions use semireducible ZMod and matrix instances.
set_option backward.isDefEq.respectTransparency false

private lemma binaryScalar_add_self (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private lemma binaryScalar_add_eq_zero (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]

private lemma binaryScalar_nonzero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a <;> norm_num at *

private lemma binaryPoint_triple_isotropic (o p x0 x1 x2 y0 y1 y2 : ZMod 2)
    (hx0 : o = 0 → x0 = 0) (hx1 : p = 0 → x1 = 0)
    (hx2 : o + p = 0 → x2 = 0) (hy0 : o = 0 → y0 = 0)
    (hy1 : p = 0 → y1 = 0) (hy2 : o + p = 0 → y2 = 0)
    (hx : x0 + x1 + x2 = 0) (hy : y0 + y1 + y2 = 0) :
    x0 * y0 + x1 * y1 + x2 * y2 = 0 := by
  fin_cases o <;> fin_cases p <;>
    simp_all [zero_add, add_zero, mul_zero, binaryScalar_add_self,
      binaryScalar_add_eq_zero]

private lemma binaryVector_add_self {ι : Type*} (x : ι → ZMod 2) : x + x = 0 := by
  funext i
  exact binaryScalar_add_self (x i)

lemma binarySupported_dot_word {ι : Type*} [Fintype ι] (x o : ι → ZMod 2)
    (hx : ∀ i, o i = 0 → x i = 0) : x ⬝ᵥ o = ∑ i, x i := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases ho : o i = 0
  · rw [ho, hx i ho]
    simp
  · rw [binaryScalar_nonzero (o i) ho, mul_one]

lemma binaryWord_dot_self {ι : Type*} [Fintype ι] (o : ι → ZMod 2) :
    o ⬝ᵥ o = ∑ i, o i := by
  exact binarySupported_dot_word o o (fun i h => h)

private lemma binaryTwo_parity_isotropic (α β γ δ m n : ZMod 2)
    (hx : α * m + β * n = 0) (hy : γ * m + δ * n = 0) :
    α * γ * m + β * δ * n = 0 := by
  fin_cases m <;> fin_cases n <;>
    simp_all [zero_add, add_zero, mul_zero, mul_one, binaryScalar_add_self,
      binaryScalar_add_eq_zero]

/-- The physical isotropy identity, with explicit coefficients in the two-word span. -/
theorem binaryTriple_physical_isotropic {ι : Type*} [Fintype ι]
    (o p x0 x1 x2 y0 y1 y2 : ι → ZMod 2) (α β γ δ : ZMod 2)
    (hx0 : ∀ i, o i = 0 → x0 i = 0) (hx1 : ∀ i, p i = 0 → x1 i = 0)
    (hx2 : ∀ i, o i + p i = 0 → x2 i = 0)
    (hy0 : ∀ i, o i = 0 → y0 i = 0) (hy1 : ∀ i, p i = 0 → y1 i = 0)
    (hy2 : ∀ i, o i + p i = 0 → y2 i = 0)
    (hx0even : (∑ i, x0 i) = 0) (hx1even : (∑ i, x1 i) = 0)
    (hx2even : (∑ i, x2 i) = 0) (hy0even : (∑ i, y0 i) = 0)
    (hy1even : (∑ i, y1 i) = 0) (hy2even : (∑ i, y2 i) = 0)
    (hx : x0 + x1 + x2 = α • o + β • p)
    (hy : y0 + y1 + y2 = γ • o + δ • p) :
    (∑ i : ι, (x0 i * y0 i + x1 i * y1 i + x2 i * y2 i)) = 0 := by
  have hxg : (x0 + α • o) + (x1 + β • p) + x2 = 0 := by
    calc
      _ = (x0 + x1 + x2) + (α • o + β • p) := by abel
      _ = (α • o + β • p) + (α • o + β • p) := by rw [hx]
      _ = 0 := binaryVector_add_self _
  have hyg : (y0 + γ • o) + (y1 + δ • p) + y2 = 0 := by
    calc
      _ = (y0 + y1 + y2) + (γ • o + δ • p) := by abel
      _ = (γ • o + δ • p) + (γ • o + δ • p) := by rw [hy]
      _ = 0 := binaryVector_add_self _
  have hpoint (i : ι) :
      (x0 + α • o) i * (y0 + γ • o) i +
        (x1 + β • p) i * (y1 + δ • p) i + x2 i * y2 i = 0 := by
    apply binaryPoint_triple_isotropic (o i) (p i)
    · intro ho
      simp [Pi.add_apply, Pi.smul_apply, ho, hx0 i ho]
    · intro hp
      simp [Pi.add_apply, Pi.smul_apply, hp, hx1 i hp]
    · exact hx2 i
    · intro ho
      simp [Pi.add_apply, Pi.smul_apply, ho, hy0 i ho]
    · intro hp
      simp [Pi.add_apply, Pi.smul_apply, hp, hy1 i hp]
    · exact hy2 i
    · exact congrFun hxg i
    · exact congrFun hyg i
  have hg : (x0 + α • o) ⬝ᵥ (y0 + γ • o) +
      (x1 + β • p) ⬝ᵥ (y1 + δ • p) + x2 ⬝ᵥ y2 = 0 := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun i _ => hpoint i)
  have hxo : x0 ⬝ᵥ o = 0 := (binarySupported_dot_word x0 o hx0).trans hx0even
  have hxp : x1 ⬝ᵥ p = 0 := (binarySupported_dot_word x1 p hx1).trans hx1even
  have hyo : o ⬝ᵥ y0 = 0 := by
    rw [dotProduct_comm]
    exact (binarySupported_dot_word y0 o hy0).trans hy0even
  have hyp : p ⬝ᵥ y1 = 0 := by
    rw [dotProduct_comm]
    exact (binarySupported_dot_word y1 p hy1).trans hy1even
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hxo, hxp, hyo, hyp, mul_zero, zero_add, add_zero,
    binaryWord_dot_self] at hg
  have hα : α * (∑ i, o i) + β * (∑ i, p i) = 0 := by
    have h := congrArg (fun z : ι → ZMod 2 => ∑ i, z i) hx
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx0even, hx1even, hx2even, add_zero] using h.symm
  have hγ : γ * (∑ i, o i) + δ * (∑ i, p i) = 0 := by
    have h := congrArg (fun z : ι → ZMod 2 => ∑ i, z i) hy
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hy0even, hy1even, hy2even, add_zero] using h.symm
  have hc := binaryTwo_parity_isotropic α β γ δ (∑ i, o i) (∑ i, p i) hα hγ
  have hdot : x0 ⬝ᵥ y0 + x1 ⬝ᵥ y1 + x2 ⬝ᵥ y2 = 0 := by
    linear_combination hg - hc
  simpa only [dotProduct, Finset.sum_add_distrib] using hdot

theorem octadTriple_physical_isotropic {ι : Type*} [Fintype ι]
    (o p : ι → ZMod 2) (x y : Fin 3 → ι → ZMod 2) (α β γ δ : ZMod 2)
    (hx : ∀ s i, (if s = 0 then o i else if s = 1 then p i else o i + p i) = 0 →
      x s i = 0)
    (hy : ∀ s i, (if s = 0 then o i else if s = 1 then p i else o i + p i) = 0 →
      y s i = 0)
    (hxeven : ∀ s, (∑ i, x s i) = 0) (hyeven : ∀ s, (∑ i, y s i) = 0)
    (hxsum : x 0 + x 1 + x 2 = α • o + β • p)
    (hysum : y 0 + y 1 + y 2 = γ • o + δ • p) :
    (∑ s : Fin 3, ∑ i : ι, x s i * y s i) = 0 := by
  have h := binaryTriple_physical_isotropic o p (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    α β γ δ
    (fun i hi => hx 0 i (by simpa using hi))
    (fun i hi => hx 1 i (by simpa using hi))
    (fun i hi => hx 2 i (by simpa using hi))
    (fun i hi => hy 0 i (by simpa using hi))
    (fun i hi => hy 1 i (by simpa using hi))
    (fun i hi => hy 2 i (by simpa using hi))
    (hxeven 0) (hxeven 1) (hxeven 2) (hyeven 0) (hyeven 1) (hyeven 2) hxsum hysum
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Finset.sum_add_distrib, add_assoc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using h

/-- Supported even triples whose totals lie in the two-word span pair to zero. -/
theorem octadTriple_physical_isotropic_of_span {ι : Type*} [Fintype ι]
    (o p : ι → ZMod 2) (x y : Fin 3 → ι → ZMod 2)
    (hx : ∀ s i, (if s = 0 then o i else if s = 1 then p i else o i + p i) = 0 →
      x s i = 0)
    (hy : ∀ s i, (if s = 0 then o i else if s = 1 then p i else o i + p i) = 0 →
      y s i = 0)
    (hxeven : ∀ s, (∑ i, x s i) = 0) (hyeven : ∀ s, (∑ i, y s i) = 0)
    (hxsum : x 0 + x 1 + x 2 ∈ Submodule.span (ZMod 2) {o, p})
    (hysum : y 0 + y 1 + y 2 ∈ Submodule.span (ZMod 2) {o, p}) :
    (∑ s : Fin 3, ∑ i : ι, x s i * y s i) = 0 := by
  obtain ⟨α, β, hxsum⟩ := Submodule.mem_span_pair.mp hxsum
  obtain ⟨γ, δ, hysum⟩ := Submodule.mem_span_pair.mp hysum
  exact octadTriple_physical_isotropic o p x y α β γ δ hx hy hxeven hyeven
    hxsum.symm hysum.symm
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
