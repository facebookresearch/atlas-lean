/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Exp

namespace MetaMathlibExt

@[expose] public section

/-- A linear chord diagram on the `2n` vertices `0, …, 2n - 1` (laid out on a line), encoded
as its fixed-point-free involution `σ`: vertex `i` is joined by a chord to `σ i`.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (linear chord diagrams on `2n` vertices). -/
def IsLinearChordDiagram (n : ℕ) (σ : Fin (2 * n) → Fin (2 * n)) : Prop :=
  ∀ i, σ i ≠ i ∧ σ (σ i) = i

instance (n : ℕ) : DecidablePred (IsLinearChordDiagram n) := fun σ => by
  unfold IsLinearChordDiagram; infer_instance

/-- Vertex `i` is an endpoint of a short chord, i.e. of a chord joining adjacent vertices.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Abstract and Section 1 (short chords). -/
def IsShortChordVertex {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (i : Fin (2 * n)) : Prop :=
  (σ i : ℕ) + 1 = i ∨ (i : ℕ) + 1 = σ i

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) : DecidablePred (IsShortChordVertex σ) :=
  fun i => by unfold IsShortChordVertex; infer_instance

/-- The vertices `a, a + 1, …, a + p - 1` (`p ≥ 1`) form a bubble of size `p`: none of them is an
endpoint of a short chord, and the run is bounded on each side by a short-chord endpoint or by
an end of the diagram (a maximal run of vertices devoid of short chords).

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of bubbles and their size). -/
def IsBubble {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (a p : ℕ) : Prop :=
  0 < p ∧ a + p ≤ 2 * n ∧
    (∀ i : Fin (2 * n), a ≤ (i : ℕ) → (i : ℕ) < a + p → ¬ IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) + 1 = a → IsShortChordVertex σ i) ∧
    (∀ i : Fin (2 * n), (i : ℕ) = a + p → IsShortChordVertex σ i)

instance {n : ℕ} (σ : Fin (2 * n) → Fin (2 * n)) (p : ℕ) :
    DecidablePred (fun a => IsBubble σ a p) := fun a => by
  unfold IsBubble; infer_instance

/-- `B_{n,p}`: the total number of bubbles of size `p` counted across all linear chord diagrams
on `2n` vertices.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Section 1 (definition of `B_{n,p}`, Table 1). -/
def bubbleCount (n p : ℕ) : ℕ :=
  ∑ σ ∈ Finset.univ.filter (IsLinearChordDiagram n),
    ((Finset.range (2 * n)).filter (fun a => IsBubble σ a p)).card

/-- `B_{1,1} = 0`: the only diagram on two vertices is one short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 1`). -/
theorem bubbleCount_one_one : bubbleCount 1 1 = 0 := by decide +kernel

/-- `B_{2,1} = 2`.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_one : bubbleCount 2 1 = 2 := by decide +kernel

/-- `B_{2,4} = 1`: the crossing diagram on four vertices has no short chord.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Table 1 (row `n = 2`). -/
theorem bubbleCount_two_four : bubbleCount 2 4 = 1 := by decide +kernel

/-- Total number of bubbles: for `n ≥ 2`,
`∑_{p=1}^{2n} B_{n,p} = (2n-2)! (4n-5) / (2^{n-1} (n-1)!)`.
The hypothesis `n ≥ 2` is added: for `n = 1` the left side is `0` and the right side is `-1`.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 3 (`jis-2024-24.4.2-lem-3`). -/
public theorem_wanted sum_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      (2 * n - 2).factorial * (4 * n - 5 : ℚ) / (2 ^ (n - 1) * (n - 1).factorial)

/-- Un-normalized first moment of bubble size: for `n ≥ 2`,
`∑_{p=1}^{2n} p B_{n,p} = (2n-1)! / (2^{n-2} (n-2)!)`.
The hypothesis `n ≥ 2` is added (the right side involves `(n-2)!`).

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 4 (`jis-2024-24.4.2-lem-4`). -/
public theorem_wanted sum_mul_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) =
      (2 * n - 1).factorial / (2 ^ (n - 2) * (n - 2).factorial)

/-- Mean bubble size over all bubbles on linear chord diagrams with `2n` vertices: for `n ≥ 2`,
`(∑_p p B_{n,p}) / (∑_p B_{n,p}) = 2(2n-1)(n-1) / (4n-5)`.
The hypothesis `n ≥ 2` is added: for `n = 1` there are no bubbles.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 5 (`jis-2024-24.4.2-thm-5`). -/
public theorem_wanted mean_bubble_size (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (p : ℚ) * bubbleCount n p) /
        (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      2 * (2 * n - 1) * (n - 1) / (4 * n - 5)

/-- Formal integral representation of the bubble generating function, in the termwise reading
the paper uses in its proof. With `s = t/x`, the paper's
`𝓛(t/x, w, ix/t, y) = (1 - y² L(ix/t, ty/x))⁻² (L(ix/t, wty/x) - 1)`, where
`L(x, y) = (1 - y(1 + x²y))⁻¹`, equals the power series
`G(s, w, y) = (1 - y² (1 - sy + y²)⁻¹)⁻² ((1 - wsy + w²y²)⁻¹ - 1)`, because
`(ix/t)² (ty/x) = -y`. The `x`-contour integral of `x⁻¹ e^{x²/2} G(t/x, w, y)` keeps
`t^{2k} [s^{2k}] G / (2^k k!)` and `∫₀^∞ t^{2k} e^{-t} dt = (2k)!`, as in the paper's proof, so
the theorem says: the coefficient of `y^{2n} w^p` of `∑_k (2k)!/(2^k k!) [s^{2k}] G` is
`B_{n,p}` for every `n, p ≥ 0` (also `n = 0`), and every odd power of `y` cancels.
Here `s, w, y` are the variables `0, 1, 2`. The literal integrals diverge; the paper's abstract
calls the result a formal generating function.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 1 (`jis-2024-24.4.2-thm-1`). -/
public theorem_wanted bubbleCount_formal_contour_integral :
    let s : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let G : MvPowerSeries (Fin 3) ℚ :=
      ((1 - y ^ 2 * (1 - s * y + y ^ 2)⁻¹) ^ 2)⁻¹ * ((1 - w * s * y + w ^ 2 * y ^ 2)⁻¹ - 1)
    (∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n)) G) = bubbleCount n p) ∧
    ∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n + 1)) G) = 0

/-- Closed form of the bubble generating function `B(y, w) = ∑_{n,p} B_{n,p} yⁿ wᵖ`, read as a
formal Laplace transform in `t`: expand the integrand
`(1-w)²(1-wy)² / ((1+w²y)(1-w(1-wy))²) · exp((y/2)(tw/(1+w²y))²)
+ ((2 - w(y+2)(1 + y(1 - w(2-wy)))) wy / (1-w(1-wy))² + (1-wy) t² w y³ / (1-w(1-wy))) · exp(t²y/2)`
as a power series in `t, w, y` (variables `0, 1, 2`) and replace `t^m` by
`∫₀^∞ t^m e^{-t} dt = m!`, which is how the paper's proofs of Lemmas 3 and 4 evaluate it. The
coefficient of `yⁿ wᵖ` is then `B_{n,p}` for `n ≥ 1`. Correction: the printed formula has
constant term `1` while `B_{0,0} = 0` (the paper's residue computation omits the residue `-1`
at `x = 0`; Theorem 1 gives constant term `0`), so `n = 0` is excluded.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Corollary 2 (`jis-2024-24.4.2-cor-2`). -/
public theorem_wanted bubbleCount_formal_laplace_closed_form :
    let t : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let D : MvPowerSeries (Fin 3) ℚ := 1 - w * (1 - w * y)
    let integrand : MvPowerSeries (Fin 3) ℚ :=
      (1 - w) ^ 2 * (1 - w * y) ^ 2 * ((1 + w ^ 2 * y) * D ^ 2)⁻¹ *
          PowerSeries.subst ((2⁻¹ : ℚ) • (y * (t * w * (1 + w ^ 2 * y)⁻¹) ^ 2)) (PowerSeries.exp ℚ) +
        ((2 - w * (y + 2) * (1 + y * (1 - w * (2 - w * y)))) * (D ^ 2)⁻¹ * (w * y) +
            (1 - w * y) * D⁻¹ * (t ^ 2 * w * y ^ 3)) *
          PowerSeries.subst ((2⁻¹ : ℚ) • (t ^ 2 * y)) (PowerSeries.exp ℚ)
    ∀ n p : ℕ, 1 ≤ n →
      (∑ᶠ m : ℕ, (m.factorial : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 p + Finsupp.single 2 n)
          integrand) = bubbleCount n p

/-- Asymptotic density of bubble sizes, excluding the diagrams that are themselves bubbles: for
`x ∈ (0, 2]` and sizes `p_n ≤ 2n - 2` with `p_n / (n - 1) → x`,
`(n-1) B_{n,p_n} / ∑_{p=1}^{2n-2} B_{n,p} → e(6-x) e^{-x/2} / (2(4e-2))`.
The paper writes `B_{n,x(n-1)}` with `x = p/(n-1)`; the index is not an integer for general `x`,
so the limit is read along any integer sizes `p_n` with `p_n/(n-1) → x`, the scaling the paper's
proof uses (`2n - p - O(1) ≈ (2-x) n`).

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 6 (`jis-2024-24.4.2-thm-6`). -/
public theorem_wanted tendsto_bubbleCount_density (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2)
    (p : ℕ → ℕ) (hp : ∀ n, p n ≤ 2 * n - 2)
    (hpx : Filter.Tendsto (fun n : ℕ => (p n : ℝ) / ((n : ℝ) - 1)) Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) - 1) * bubbleCount n (p n) /
        ∑ q ∈ Finset.Icc 1 (2 * n - 2), (bubbleCount n q : ℝ))
      Filter.atTop
      (nhds (Real.exp 1 * (6 - x) / (2 * (4 * Real.exp 1 - 2)) * Real.exp (-x / 2)))

end

end MetaMathlibExt
