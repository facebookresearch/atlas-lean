/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# The star–triangle transformation for inhomogeneous bond percolation

A triangle with corners `A`, `B`, `C` whose edges are open independently with probabilities
`p₀, p₁, p₂`, and a star with centre `O` whose edges `OA, OB, OC` are open with probabilities
`1 - p₀, 1 - p₁, 1 - p₂`. The star–triangle transformation compares the laws of the connectivity
pattern that each cell induces on `{A, B, C}`. This file proves the finite identities behind it:
the patterns "only `A` and `B` connected" (and the two other single pairs) have the same
probability for all parameters, while the patterns "all three connected" and "all separated"
differ by exactly `±κ(p)`, where `κ(p) = p₀ + p₁ + p₂ - p₀p₁p₂ - 1` is the criticality function of
the inhomogeneous triangular lattice. Hence all five pattern probabilities agree if and only if
`κ(p) = 0`.

Everything here is a computation over the eight states of three edges; no lattice, measure on an
infinite graph, or percolation statement is involved.

## Main definitions

* `StatMech.Universality.kappaSquare`, `kappaTri`, `kappaHex`: criticality functions of the
  inhomogeneous square, triangular and hexagonal bond models; `IsCriticalSquare` etc.
* `StatMech.Universality.LocalConfig`, `localWeight`: the states of three edges and their product
  weight.
* `StatMech.Universality.triAB`, `starAB`, ...: which corners a cell connects; `triPatABC`,
  `starPatSep`, ...: the five connectivity patterns.
* `StatMech.Universality.triProb`, `starProb`: the probability of a pattern.

## Main results

* `StatMech.Universality.stt_AB`, `stt_AC`, `stt_BC`: single-pair patterns agree for all
  parameters.
* `StatMech.Universality.stt_ABC_sub`, `stt_Sep_sub`: the other two patterns differ by `±κ(p)`.
* `StatMech.Universality.starTriangle_connectivity`,
  `StatMech.Universality.starTriangle_iff_isCriticalTri`: the star–triangle transformation holds
  exactly on the critical surface `κ(p) = 0`.
* `StatMech.Universality.bernoulliMeasure_map_not`: flipping a `Bernoulli(p)` bit gives
  `Bernoulli(1 - p)`.

## References

* M. F. Sykes, J. W. Essam, *Exact critical percolation probabilities for site and bond problems
  in two dimensions*, J. Math. Phys. 5 (1964), 1117–1127.
* G. R. Grimmett, I. Manolescu, *Inhomogeneous bond percolation on square, triangular and
  hexagonal lattices*, Ann. Probab. 41 (2013), 2990–3025.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

/-- The criticality function `p₀ + p₁ - 1` of inhomogeneous bond percolation on the square
lattice with horizontal and vertical parameters `p₀`, `p₁`. -/
def kappaSquare (p0 p1 : ℝ) : ℝ := p0 + p1 - 1

/-- The criticality function `p₀ + p₁ + p₂ - p₀p₁p₂ - 1` of inhomogeneous bond percolation on the
triangular lattice. -/
def kappaTri (p0 p1 p2 : ℝ) : ℝ := p0 + p1 + p2 - p0 * p1 * p2 - 1

/-- The criticality function of inhomogeneous bond percolation on the hexagonal lattice:
`-κ_tri(1 - p₀, 1 - p₁, 1 - p₂)`. -/
def kappaHex (p0 p1 p2 : ℝ) : ℝ := -kappaTri (1 - p0) (1 - p1) (1 - p2)

/-- The square-lattice parameters `(p₀, p₁)` lie on the critical surface `p₀ + p₁ = 1`. -/
def IsCriticalSquare (p0 p1 : ℝ) : Prop := kappaSquare p0 p1 = 0

/-- The triangular-lattice parameters lie on the critical surface `κ_tri(p) = 0`. -/
def IsCriticalTri (p0 p1 p2 : ℝ) : Prop := kappaTri p0 p1 p2 = 0

/-- The hexagonal-lattice parameters lie on the critical surface `κ_hex(p) = 0`. -/
def IsCriticalHex (p0 p1 p2 : ℝ) : Prop := kappaHex p0 p1 p2 = 0

theorem isCriticalSquare_iff (p0 p1 : ℝ) : IsCriticalSquare p0 p1 ↔ p0 + p1 = 1 := by
  unfold IsCriticalSquare kappaSquare; constructor <;> intro h <;> linarith

theorem isCriticalTri_iff (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ p0 + p1 + p2 - p0 * p1 * p2 = 1 := by
  unfold IsCriticalTri kappaTri; constructor <;> intro h <;> linarith

/-- `p` is critical for the triangular lattice iff `1 - p` is critical for the hexagonal lattice. -/
theorem isCriticalTri_iff_isCriticalHex_compl (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ IsCriticalHex (1 - p0) (1 - p1) (1 - p2) := by
  unfold IsCriticalTri IsCriticalHex kappaHex
  simp only [sub_sub_cancel]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith [neg_eq_zero.mp h]

/-- The probability `p` or `1 - p` that a `Bernoulli(p)` edge is in state `b`.

See also `StatMech.edgeWeight`, the same weight read off a coordinate of a configuration. -/
def edgeWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem edgeWeight_true (p : ℝ) : edgeWeight p true = p := rfl
@[simp] theorem edgeWeight_false (p : ℝ) : edgeWeight p false = 1 - p := rfl

/-- The states of three edges. In a triangle `ABC` the components are the edges `BC`, `AC`, `AB`;
in a star with centre `O` they are `OA`, `OB`, `OC`. -/
abbrev LocalConfig : Type := Bool × Bool × Bool

/-- The product weight of a state of three independent edges with parameters `p₀, p₁, p₂`. -/
def localWeight (p0 p1 p2 : ℝ) (ω : LocalConfig) : ℝ :=
  edgeWeight p0 ω.1 * edgeWeight p1 ω.2.1 * edgeWeight p2 ω.2.2

/-- The weights of the eight states sum to `1`. -/
theorem sum_localWeight (p0 p1 p2 : ℝ) :
    ∑ ω : LocalConfig, localWeight p0 p1 p2 ω = 1 := by
  simp only [localWeight, edgeWeight, Fintype.sum_prod_type, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false]
  ring

/-- `A` and `B` are connected in the triangle: `AB` is open, or `AC` and `BC` both are. -/
def triAB (ω : LocalConfig) : Bool := ω.2.2 || (ω.1 && ω.2.1)

/-- `A` and `C` are connected in the triangle. -/
def triAC (ω : LocalConfig) : Bool := ω.2.1 || (ω.1 && ω.2.2)

/-- `B` and `C` are connected in the triangle. -/
def triBC (ω : LocalConfig) : Bool := ω.1 || (ω.2.1 && ω.2.2)

/-- `A` and `B` are connected in the star: `OA` and `OB` are open. -/
def starAB (ω : LocalConfig) : Bool := ω.1 && ω.2.1

/-- `A` and `C` are connected in the star. -/
def starAC (ω : LocalConfig) : Bool := ω.1 && ω.2.2

/-- `B` and `C` are connected in the star. -/
def starBC (ω : LocalConfig) : Bool := ω.2.1 && ω.2.2

/-- Pattern: all three corners connected in the triangle. -/
def triPatABC (ω : LocalConfig) : Bool := triAB ω && triBC ω && triAC ω

/-- Pattern: all three corners connected in the star. -/
def starPatABC (ω : LocalConfig) : Bool := starAB ω && starBC ω && starAC ω

/-- Pattern: no two corners connected in the triangle. -/
def triPatSep (ω : LocalConfig) : Bool := !triAB ω && !triBC ω && !triAC ω

/-- Pattern: no two corners connected in the star. -/
def starPatSep (ω : LocalConfig) : Bool := !starAB ω && !starBC ω && !starAC ω

/-- Pattern: exactly `A` and `B` connected in the triangle. -/
def triPatAB (ω : LocalConfig) : Bool := triAB ω && !triAC ω && !triBC ω

/-- Pattern: exactly `A` and `B` connected in the star. -/
def starPatAB (ω : LocalConfig) : Bool := starAB ω && !starAC ω && !starBC ω

/-- Pattern: exactly `A` and `C` connected in the triangle. -/
def triPatAC (ω : LocalConfig) : Bool := triAC ω && !triAB ω && !triBC ω

/-- Pattern: exactly `A` and `C` connected in the star. -/
def starPatAC (ω : LocalConfig) : Bool := starAC ω && !starAB ω && !starBC ω

/-- Pattern: exactly `B` and `C` connected in the triangle. -/
def triPatBC (ω : LocalConfig) : Bool := triBC ω && !triAB ω && !triAC ω

/-- Pattern: exactly `B` and `C` connected in the star. -/
def starPatBC (ω : LocalConfig) : Bool := starBC ω && !starAB ω && !starAC ω

/-- The probability that three independent edges with parameters `p₀, p₁, p₂` realize `pat`. -/
def triProb (p0 p1 p2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight p0 p1 p2 ω else 0

/-- The probability that three independent edges with parameters `q₀, q₁, q₂` realize `pat`.
The same function as `triProb`; the name records that it is applied to star patterns. -/
def starProb (q0 q1 q2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight q0 q1 q2 ω else 0

/-- The triangle with parameters `p` and the star with parameters `1 - p` give the pattern
"exactly `A`, `B` connected" the same probability, for all `p`. -/
theorem stt_AB (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAB, starPatAB,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- Single-pair pattern `AC` of the star–triangle transformation; holds for all `p`. -/
theorem stt_AC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAC, starPatAC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- Single-pair pattern `BC` of the star–triangle transformation; holds for all `p`. -/
theorem stt_BC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatBC, starPatBC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- The triangle and star probabilities of "all corners connected" differ by `κ_tri(p)`. -/
theorem stt_ABC_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatABC - starProb (1 - p0) (1 - p1) (1 - p2) starPatABC
      = kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatABC, starPatABC,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- The triangle and star probabilities of "all corners separated" differ by `-κ_tri(p)`. -/
theorem stt_Sep_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatSep - starProb (1 - p0) (1 - p1) (1 - p2) starPatSep
      = -kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatSep, starPatSep,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- On the critical surface the "all connected" probabilities agree. -/
theorem stt_ABC (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC := by
  have := stt_ABC_sub p0 p1 p2
  rw [h] at this; linarith

/-- On the critical surface the "all separated" probabilities agree. -/
theorem stt_Sep (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep := by
  have := stt_Sep_sub p0 p1 p2
  rw [h] at this; linarith

/-- **Star–triangle transformation** (Sykes–Essam 1964): on the critical surface `κ_tri(p) = 0`, the
triangle with parameters `p` and the star with parameters `1 - p` induce the same law on the five
connectivity patterns of the corners. -/
theorem starTriangle_connectivity (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC ∧
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep ∧
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB ∧
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC ∧
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC :=
  ⟨stt_ABC p0 p1 p2 h, stt_Sep p0 p1 p2 h, stt_AB p0 p1 p2, stt_AC p0 p1 p2,
    stt_BC p0 p1 p2⟩

/-- Equality of the "all connected" probabilities forces `κ_tri(p) = 0`. -/
theorem isCriticalTri_of_starTriangle (p0 p1 p2 : ℝ)
    (h : triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) :
    IsCriticalTri p0 p1 p2 := by
  have := stt_ABC_sub p0 p1 p2
  rw [h, sub_self] at this
  exact this.symm

/-- The star–triangle identity for "all connected" holds iff `p` is on the critical surface. -/
theorem starTriangle_iff_isCriticalTri (p0 p1 p2 : ℝ) :
    (triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) ↔
      IsCriticalTri p0 p1 p2 :=
  ⟨isCriticalTri_of_starTriangle p0 p1 p2, stt_ABC p0 p1 p2⟩

/-- Negating a `Bernoulli(p)` bit gives a `Bernoulli(1 - p)` bit.

See also `ProbabilityTheory.map_bernoulliMeasure`. -/
theorem bernoulliMeasure_map_not (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun b => !b) (bernoulliMeasure p hp)
      = bernoulliMeasure (1 - p) tsub_le_self := by
  have hmeas : Measurable (fun b : Bool => !b) := measurable_of_countable _
  refine (MeasureTheory.Measure.ext_iff_singleton).2 ?_
  intro x
  rw [Measure.map_apply hmeas (measurableSet_singleton x)]
  cases x with
  | false =>
    have hpre : (fun b => !b) ⁻¹' ({false} : Set Bool) = ({true} : Set Bool) := by
      ext b; cases b <;> simp
    have harith : (1 : ℝ≥0) - (1 - p) = p := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub tsub_le_self, NNReal.coe_sub hp]; ring
    rw [bernoulliMeasure_apply_false, harith, hpre, bernoulliMeasure_apply_true]
  | true =>
    have hpre : (fun b => !b) ⁻¹' ({true} : Set Bool) = ({false} : Set Bool) := by
      ext b; cases b <;> simp
    rw [bernoulliMeasure_apply_true, hpre, bernoulliMeasure_apply_false,
      ENNReal.coe_sub, ENNReal.coe_one]

/-- `1 - 1/2 = 1/2` in `ℝ≥0`. -/
theorem one_sub_half : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (by norm_num)]; push_cast; norm_num

/-- `1/2 ≤ 1` in `ℝ≥0`, the bound needed to form `bernoulliMeasure 2⁻¹`. -/
theorem half_le_one : (2 : ℝ≥0)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (by norm_num)]; norm_num

/-- The fair coin is invariant under negation. -/
theorem bernoulli_selfDual_half :
    Measure.map (fun b => !b) (bernoulliMeasure 2⁻¹ half_le_one)
      = bernoulliMeasure 2⁻¹ half_le_one := by
  rw [bernoulliMeasure_map_not]
  congr 1
  exact one_sub_half

end Universality

end StatMech
