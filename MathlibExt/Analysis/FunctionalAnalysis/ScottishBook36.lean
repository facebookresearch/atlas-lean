/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-!
# Retraction onto the unit sphere of a Hilbert space

Every infinite-dimensional real Hilbert space retracts onto its unit sphere. We use the
unilateral shift on a copy of `ℓ²(ℕ, ℝ)` to perturb the identity away from zero, then normalize.
-/

public section

universe u

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted

open scoped _root_.lp ENNReal
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

private theorem exists_l2_isometry (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (hE : ¬ Module.Finite ℝ E) : Nonempty (ℓ²(ℕ, ℝ) →ₗᵢ[ℝ] E) := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℝ E
  have : Infinite ι := by
    apply not_finite_iff_infinite.mp
    intro h
    let := Fintype.ofFinite ι
    exact hE (Module.Basis.finiteDimensional_of_finite b.toOrthonormalBasis.toBasis)
  let e := Infinite.natEmbedding ι
  exact ⟨(b.orthonormal.comp e e.injective).orthogonalFamily.linearIsometry⟩

-- Inserting c before the scaled shift gives the recurrence z₀ = c, zₙ₊₁ = t zₙ.
-- If t c = c, its only square-summable solution is zero.
private theorem shift_fixed_eq_zero (z : ℓ²(ℕ, ℝ)) (t c : ℝ) (htc : t * c = c)
    (hz : z = t • shiftCLM z + lp.single 2 0 c) : z = 0 ∧ c = 0 := by
  have coord (n : ℕ) : z n = t * shiftFun (⇑z) n + (Pi.single 0 c : ℕ → ℝ) n :=
    congrArg (fun y : ℓ²(ℕ, ℝ) => y n) hz
  have h (n : ℕ) : z n = c := by
    induction n with
    | zero => simpa using coord 0
    | succ n ih => simpa [ih, htc] using coord (n + 1)
  have hs := (lp.memℓp z).summable (by simp : 0 < (2 : ℝ≥0∞).toReal)
  have hc : c = 0 := by simpa [h, summable_const_iff] using hs
  exact ⟨lp.ext (funext fun n => (h n).trans hc), hc⟩

/--
**Retraction onto the unit sphere of Hilbert space.** Let $E$ be an infinite-dimensional real
Hilbert space and let $S = \{x \in E : \|x\| = 1\}$ be its unit sphere. Then there is a
continuous map $f : E \to E$ such that $f(x) \in S$ for every $x \in E$ and $f(x) = x$ for every
$x \in S$.

Restricting $f$ to the closed unit ball gives a retraction of the ball onto $S$; conversely, a
retraction $r$ of the closed unit ball onto $S$ extends to all of $E$ by
$f(x) = r(x / \max(1, \|x\|))$. In finite dimensions no such map exists, by the Brouwer
no-retraction theorem, so the infinite-dimensional hypothesis is essential.

Source: S. Ulam, Problem 36 of the Scottish
Book, asking whether there is a retraction of the closed unit ball of Hilbert
space onto its boundary; the answer is affirmative, see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015), and the
2026 survey "90+ years of the Scottish Book" (arXiv:2603.27867), which notes
that the unit sphere of a Hilbert space is homeomorphic to the whole space.
-/
theorem hilbertBallRetractsOntoSphere :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∃ f : E → E, Continuous f ∧ (∀ x, f x ∈ Metric.sphere (0 : E) 1) ∧
        ∀ x ∈ Metric.sphere (0 : E) 1, f x = x := by
  intro E _ _ _ hE
  obtain ⟨j⟩ := exists_l2_isometry E hE
  let p := j.toContinuousLinearMap.adjoint
  have hp (z : ℓ²(ℕ, ℝ)) : p (j z) = z := DFunLike.congr_fun j.adjoint_comp_self z
  -- Moving inward from the unit sphere, first turn on the shift, then fill its zeroth
  -- coordinate. Thus the inserted coordinate can be nonzero only at full shift strength.
  let s (x : E) := 2 * max (1 - ‖x‖) 0
  let t (x : E) := min (s x) 1
  let c (x : E) := max (s x - 1) 0
  let insert := lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 0
  let v (x : E) := t x • shiftCLM (p x) + insert (c x)
  let g (x : E) := x - j (v x)
  have hs : Continuous s := by
    unfold s
    fun_prop
  have ht : Continuous t := hs.min continuous_const
  have hc : Continuous c := (hs.sub continuous_const).max continuous_const
  have hv : Continuous v :=
    (ht.smul (shiftCLM.continuous.comp p.continuous)).add (insert.continuous.comp hc)
  have hg : Continuous g := continuous_id.sub (j.continuous.comp hv)
  have hne (x : E) : g x ≠ 0 := by
    intro h
    have hx : x = j (v x) := sub_eq_zero.mp h
    have hpv : p x = v x := (congrArg p hx).trans (hp _)
    have htc : t x * c x = c x := by
      rcases le_total (s x) 1 with h | h
      · simp [c, max_eq_right (sub_nonpos.mpr h)]
      · simp [t, min_eq_right h]
    obtain ⟨hz, hc0⟩ := shift_fixed_eq_zero (p x) (t x) (c x) htc hpv
    have hx0 : x = 0 := by simpa [← hpv, hz] using hx
    norm_num [hx0, c, s] at hc0
  refine ⟨fun x => NormedSpace.normalize (g x), ?_, ?_, ?_⟩
  · exact (hg.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hne x)).smul hg
  · exact fun x => mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hne x))
  · intro x hx
    have hnorm := mem_sphere_zero_iff_norm.mp hx
    simpa [g, v, t, c, s, hnorm] using NormedSpace.normalize_eq_self_of_norm_eq_one hnorm

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted
