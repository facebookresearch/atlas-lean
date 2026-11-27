/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Correlation polynomials, pattern avoidance and Conway's waiting-time odds

Guibas and Odlyzko, as presented by Odlyzko (1985): let `A` be a word of length `k ≥ 1` over an
alphabet of `q ≥ 2` letters and `f(n)` the number of words of length `n` with no occurrence of `A`
as a contiguous factor. The autocorrelation of `A` records the borders of `A`: the lengths
`1 ≤ r ≤ k` whose length-`r` prefix equals the length-`r` suffix (`r = k` always counts). As a
polynomial, `AA_z = ∑_{r border} z^{r-1}`. For two words `A` and `B`, the suffix–prefix overlap
polynomial `corr A B z` sums `z^{r-1}` over the `r ≤ min(|A|, |B|)` for which the length-`r`
suffix of `A` equals the length-`r` prefix of `B`. In the cases used here, the autocorrelation of
a nonempty word and two words neither of which is a factor of the other, it is the correlation
`AB_z` of Odlyzko (1985, Section 3), but not for arbitrary pairs: Section 3 also counts each
occurrence of `B` inside `A` that ends before the last letter of `A`, so for `A = ab` and `B = a`
it gives `AB_2 = 2`, while `corr A B 2 = 0`. With `F(z) = ∑_n f(n) z^{-n}`,

  `F(z) = z AA_z / (1 + (z - q) AA_z)`.

Here the identity is stated for formal power series in `x = z⁻¹`: multiplying numerator and
denominator by `x^k = z^{-k}` gives `F · (x^k + (1 - q x) c(x)) = c(x)` with
`c(x) = x^{k-1} AA_{1/x} = ∑_{r border} x^{k-r}`, a polynomial. Consequences for i.i.d. uniform
letters: the expected waiting time until `A` first appears is `F(q) = q AA_q = ∑_{r border} q^r`;
and for two words `A`, `B` over a two-letter alphabet, neither a factor of the other, Conway's
odds that `B` appears before `A` are `(AA_2 - AB_2) : (BB_2 - BA_2)`.

Positions are `0`-based. The waiting time `T_A` is the least `n ≥ k` such that letters
`n - k, …, n - 1` spell `A` (`⊤` if there is none).

Sources: A. M. Odlyzko, "Enumeration of strings", in *Combinatorial Algorithms on Words*
(A. Apostolico and Z. Galil, eds.), NATO ASI Series F12, Springer, 1985, 205–228, presenting
L. J. Guibas and A. M. Odlyzko, "String overlaps, pattern matching, and nontransitive games",
Journal of Combinatorial Theory, Series A 30 (1981) 183–208, doi:10.1016/0097-3165(81)90005-4;
and L. J. Guibas and A. M. Odlyzko, "Periods in strings", Journal of Combinatorial Theory,
Series A 30 (1981) 19–42.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.ProductMeasure
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.StringCorrelationWanted

open MeasureTheory

variable {α : Type*} [DecidableEq α]

/-- **Suffix–prefix overlap set.** The lengths `1 ≤ r ≤ min(|A|, |B|)` for which the length-`r`
suffix of `A` equals the length-`r` prefix of `B`. For `A = B ≠ []` these are the borders of `A`,
including `r = |A|`; `corrSet [] []` is empty. In the cases used here, the autocorrelation of a
nonempty word and two words neither of which is a factor of the other, they are the positions of
Odlyzko's correlation `AB` (1985, Section 3), counted by overlap length; for other pairs that
correlation also has a position for each occurrence of `B` inside `A` that ends before the last
letter of `A`. -/
def corrSet (A B : List α) : Finset ℕ :=
  (Finset.Icc 1 (min A.length B.length)).filter fun r => A.drop (A.length - r) = B.take r

/-- **Suffix–prefix overlap polynomial.** `∑_{r ∈ corrSet A B} z^{r-1}`, evaluated at `z`. In the
cases used here, the autocorrelation of a nonempty word and two words neither of which is a factor
of the other, it is Odlyzko's correlation `AB_z` (1985, Section 3), but not for arbitrary pairs:
for `A = ab` and `B = a`, Section 3 gives `AB_2 = 2`, counting the occurrence of `B` at the start
of `A`, while `corr A B 2 = 0`. -/
def corr (A B : List α) (z : ℚ) : ℚ :=
  ∑ r ∈ corrSet A B, z ^ (r - 1)

/-- `A` occurs in the word `w` as a contiguous factor. -/
def Occurs (A : List α) (w : List α) : Prop :=
  A <:+: w

variable [Fintype α]

open Classical in
/-- `f(n)`: the number of words of length `n` over `α` with no occurrence of `A`. -/
noncomputable def avoidCount (A : List α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → α => ¬ Occurs A (List.ofFn w)).card

/-- The polynomial `c(x) = ∑_{r border of A} x^{|A| - r}` as a power series. -/
noncomputable def corrSeries (A : List α) : PowerSeries ℤ :=
  ∑ r ∈ corrSet A A, PowerSeries.X ^ (A.length - r)

/-- **The avoidance generating function** (Guibas–Odlyzko, in Odlyzko 1985): for a word `A` of
length `k ≥ 1` over an alphabet of `q = |α| ≥ 2` letters, the series `G(x) = ∑_n f(n) x^n`
satisfies `G(x) · (x^k + (1 - q x) c(x)) = c(x)`, where `c(x) = ∑_{r border of A} x^{k-r}`;
with `x = 1 / z` this is `F(z) = z AA_z / (1 + (z - q) AA_z)`.

Source: Odlyzko (1985), presenting Guibas and Odlyzko (1981). -/
public theorem_wanted avoidSeries_mul_eq (A : List α) (hA : A ≠ []) (hq : 2 ≤ Fintype.card α) :
    PowerSeries.mk (fun n => (avoidCount A n : ℤ)) *
        (PowerSeries.X ^ A.length + (1 - (Fintype.card α : PowerSeries ℤ) * PowerSeries.X) *
          corrSeries A) = corrSeries A

/-- **Uniform letter law.** Every letter has mass `1 / |α|` under `ν`. For a probability measure
`ν`, as in the theorems below, this says that `ν` is the uniform law on the finite alphabet `α`. -/
def IsUniformLetterLaw [MeasurableSpace α] (ν : Measure α) : Prop :=
  ∀ a : α, ν {a} = (Fintype.card α : ENNReal)⁻¹

/-- The law of an infinite i.i.d. text `ℕ → α` with letter law `ν`. -/
noncomputable def textLaw [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] :
    Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The **waiting time** `T_A(ω)`: the least `n ≥ |A|` such that letters `n - |A|, …, n - 1` of
`ω` spell `A`, and `⊤` if there is none. -/
noncomputable def waitingTime (A : List α) (ω : ℕ → α) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : A.length ≤ n ∧ (List.range A.length).map (fun i => ω (n - A.length + i)) = A),
    (n : ℕ∞)

/-- **Expected waiting time** (Guibas–Odlyzko, in Odlyzko 1985): for i.i.d. letters over an
alphabet of `q = |α| ≥ 2` letters with the discrete measurable structure, each letter having
probability `1 / q` under the probability measure `ν`, and a nonempty word `A`, the expected
waiting time until `A` first appears is `F(q) = q AA_q = ∑_{r border of A} q^r`.

Source: Odlyzko (1985), presenting Guibas and Odlyzko (1981). -/
public theorem_wanted lintegral_waitingTime [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (hν : IsUniformLetterLaw ν)
    (hq : 2 ≤ Fintype.card α) (A : List α) (hA : A ≠ []) :
    ∫⁻ ω, ((waitingTime A ω : ℕ∞) : ENNReal) ∂textLaw ν =
      ∑ r ∈ corrSet A A, (Fintype.card α : ENNReal) ^ r

/-- **Conway's odds for Penney's game** (Guibas–Odlyzko, in Odlyzko 1985): for i.i.d. fair
binary letters (each of the two letters has probability `1 / 2` under the probability measure
`ν`) and two nonempty words `A`, `B` over `Bool`, neither a factor of the other,
`P(T_B < T_A) · (BB_2 - BA_2) = P(T_A < T_B) · (AA_2 - AB_2)`; that is, the odds that `B`
appears before `A` are `(AA_2 - AB_2) : (BB_2 - BA_2)`. Here `XY_2` is `corr X Y 2`, which for
such words is Odlyzko's correlation.

Source: Odlyzko (1985), presenting Guibas and Odlyzko (1981). -/
public theorem_wanted conway_odds (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hν : IsUniformLetterLaw ν) (A B : List Bool) (hA : A ≠ []) (hB : B ≠ [])
    (hAB : ¬ Occurs A B) (hBA : ¬ Occurs B A) :
    (textLaw ν {ω | waitingTime B ω < waitingTime A ω}).toReal *
        ((corr B B 2 - corr B A 2 : ℚ) : ℝ) =
      (textLaw ν {ω | waitingTime A ω < waitingTime B ω}).toReal *
        ((corr A A 2 - corr A B 2 : ℚ) : ℝ)

end WantedExt.Biology.ComputationalBiology.StringCorrelationWanted
