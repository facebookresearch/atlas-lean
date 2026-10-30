/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Toeplitz-Hessenberg determinants with Fuss-Catalan entries

Statements from Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2.

`toeplitzHessenbergDet a n` is the determinant of the `n × n` Toeplitz-Hessenberg matrix with
`a 0` on the superdiagonal and `a 1, …, a n` down the first column. The paper's
`D_±(a_1, …, a_n)` is `toeplitzHessenbergDet (fun i => if i = 0 then ±1 else a i) n`.
The Fuss-Catalan (Raney) number `A_n(p, r)` is `(generalizedFussCatalanNumber p n r : ℚ)`
(MathlibExt), so `C_n = A_n(2, 1)`,
`K_n = A_n(2, 3) = C_{n+2} - C_{n+1}`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`. The Catalan generating
function `C(x)` is `PowerSeries.mk fun n => (catalan n : ℚ)`. Generating-function statements are
written multiplicatively.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK

namespace MetaMathlibExt

@[expose] public section

/-- Small values: `A_3(2, 1) = C_3 = 5`, `A_2(2, 3) = K_2 = C_4 - C_3 = 9`, `A_3(3, 1) = 12`,
`A_2(3, 2) = 7`.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Sections 1-2
(`C_n = A_n(2, 1)`, `K_n = A_n(2, 3)`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`). -/
theorem toeplitzHessenberg_fussCatalan_examples :
    generalizedFussCatalanNumber 2 3 1 = 5 ∧ generalizedFussCatalanNumber 2 2 3 = 9 ∧
      generalizedFussCatalanNumber 3 3 1 = 12 ∧ generalizedFussCatalanNumber 3 2 2 = 7 := by
  decide

/-- With `f(x) = ∑_{n ≥ 1} det(A_n) xⁿ` and `g(x) = ∑_{i ≥ 1} aᵢ xⁱ`,
`f(x) = (-g(-a_0 x)/a_0)/(1 + g(-a_0 x)/a_0)`. Writing
`H(x) = -g(-a_0 x)/a_0 = ∑_{i ≥ 1} aᵢ (-a_0)^{i-1} xⁱ`, this is `f = H/(1 - H)`, stated
denominator-free as `f = H + H f`. This form holds over any commutative ring without the paper's
hypothesis `a_0 ≠ 0`; at `a_0 = 0` it reads `H = a_1 x` and `det(A_n) = a_1ⁿ`.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 2
(`jis-2026-26.1.2-lem-2`). -/
public theorem_wanted toeplitzHessenbergDet_genFun {R : Type*} [CommRing R] (a : ℕ → R) :
    PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n) =
      PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) +
        PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) *
          PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n)

/-- For all integers `p, r ≥ 0` and `n ≥ 1`,
`D_+(A_1(p, r), …, A_n(p, r)) = (-1)^{n-1} (r/n) C(pn - r - 1, n - 1)`, the binomial coefficient
taken with integer (possibly negative) upper index. Theorem 3 assumes `p, r ≥ 0`; the paper's
standing assumption (Section 1) that `p` and `r` are not both zero is dropped: at `p = r = 0` every
entry `A_i(0, 0)` is `0` and both sides vanish.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 3
(`jis-2026-26.1.2-thm-3`). -/
public theorem_wanted toeplitzHessenbergDet_fussCatalan (p r n : ℕ) (hn : 1 ≤ n) :
    toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      (-1) ^ (n - 1) * (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ)

/-- Special cases of Theorem 3:
`(-1)^{n-1} D_+(A_1(2,3), …, A_n(2,3)) = C_{n-1} - C_{n-2}` for `n ≥ 2`,
`(-1)^{n-1} D_+(A_1(2,4), …, A_n(2,4)) = C_{n-1} - 2C_{n-2}` for `n ≥ 3`,
`(-1)^{n-1} D_+(A_1(3,1), …, A_n(3,1)) = (1/n) C(3n-2, n-1)` and
`(-1)^{n-1} D_+(A_1(3,2), …, A_n(3,2)) = (2/n) C(3n-3, n-1)` for `n ≥ 1`. The OEIS
identifications (A000245, A115143, A006013, A007226) are omitted.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 4
(`jis-2026-26.1.2-cor-4`). -/
public theorem_wanted toeplitzHessenbergDet_fussCatalan_special :
    (∀ n : ℕ, 2 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 3 : ℚ)) n =
        (catalan (n - 1) : ℚ) - catalan (n - 2)) ∧
    (∀ n : ℕ, 3 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 2 i 4 : ℚ)) n =
        (catalan (n - 1) : ℚ) - 2 * catalan (n - 2)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 1 : ℚ)) n =
        1 / (n : ℚ) * ((3 * n - 2).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (-1) ^ (n - 1) * toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 i 2 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)

/-- Catalan determinants, with `C(x) = ∑ Cₙ xⁿ` and `K_m = C_{m+2} - C_{m+1}`:
1. `∑_{n ≥ 1} D_-(C_1, C_3, …, C_{2n-1}) y^{2n} = y² C(y)² C(-y)²`, i.e. `D_-(C_1, …, C_{2n-1})` is
   the sequence A066357 through the generating function `x C²(x^{1/2}) C²(-x^{1/2})` recalled in
   the paper's proof;
2. `1 + ∑_{n ≥ 1} D_-(C_2, …, C_{n+1}) xⁿ = 1/(2 - C²)` (the paper's definition of `p_n`), stated
   as `(∑_{n ≥ 0} D_-(C_2, …, C_{n+1}) xⁿ)(2 - C²) = 1` (the `0 × 0` determinant is `1`);
3. `D_+(K_{-1}, K_0, …, K_{n-2}) = (-1)^{n-1} ∑_{i=1}^{n-1} C_i` for `n ≥ 1`;
4. `D_+(K_0, K_1, …, K_{n-1}) = (-1)^{n-1} ∑_{i=0}^{n-1} C_i` for `n ≥ 1`;
5. `∑_{n ≥ 1} D_-(K_0, …, K_{n-1}) xⁿ = xC³/(1 - xC³)`, the generating function of A026674 used in
   the paper's proof, stated multiplicatively.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 6
(`jis-2026-26.1.2-thm-6`). -/
public theorem_wanted toeplitzHessenbergDet_catalan :
    let C : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)
    (PowerSeries.mk (fun m => if m % 2 = 0 ∧ 2 ≤ m then
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)) (m / 2)
      else 0) =
      PowerSeries.X ^ 2 * C ^ 2 * (PowerSeries.rescale (-1 : ℚ) C) ^ 2) ∧
    (PowerSeries.mk (fun n =>
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)) n) *
      (2 - C ^ 2) = 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else
        toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i) n) *
      (1 - PowerSeries.X * C ^ 3) = PowerSeries.X * C ^ 3

/-- With `H_n = A_n(3, 1)` and `J_n = A_n(3, 2)`:
`D_+(H_2, H_3, …, H_{n+1}) = 2(-1)^{n-1}/n · C(3n - 3, n - 1)` for `n ≥ 2`, and
`D_-(J_0, J_1, …, J_{n-1}) = H_n` for `n ≥ 1`. The formulas for `D_+(H_0, …, H_{n-1})`,
`D_-(H_0, …, H_{n-1})`, `D_-(H_1, …, H_n)` and `D_+(J_0, …, J_{n-1})` are omitted: their values
are the OEIS entries A023053, A098746, A047099, A121545, which the paper does not define.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 8, formulas
(4) and (6) (`jis-2026-26.1.2-thm-8`). -/
public theorem_wanted toeplitzHessenbergDet_ternary :
    (∀ n : ℕ, 2 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 * (-1) ^ (n - 1) / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ)

/-- Multi-sum forms (via Trudi's formula) of the explicit formulas:
`∑_{α̃ = n} (-1)^{|α|-1} m_n(α) A_1(p,r)^{α₁} ⋯ A_n(p,r)^{αₙ} = (r/n) C(pn - r - 1, n - 1)`,
the `K_{-1}, …, K_{n-2}` and `K_0, …, K_{n-1}` sums `∑_{i=1}^{n-1} C_i` and `∑_{i=0}^{n-1} C_i`
(`n ≥ 1`), the `H_2, …, H_{n+1}` sum `(2/n) C(3n - 3, n - 1)` (`n ≥ 2`, the closed form of
A007226(n - 1) from Theorem 8), and the unsigned `J_0, …, J_{n-1}` sum `H_n` (`n ≥ 1`). The lines
whose right sides are A066357, `p_n`, A026674, A023053, A098746, A047099, A121545 are omitted (the
first three are given in the paper only through generating functions, already stated in
`toeplitzHessenbergDet_catalan`; the others are not defined in the paper). As in
`toeplitzHessenbergDet_fussCatalan`, the first sum includes `p = r = 0`, which the paper's standing
assumption excludes; there both sides are `0`.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 9
(`jis-2026-26.1.2-cor-9`). -/
public theorem_wanted trudiPartitionSum_fussCatalan :
    (∀ p r n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber p i r : ℚ)) n =
        (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan i : ℚ) - catalan (i - 1)) n =
        ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan (i + 1) : ℚ) - catalan i) n =
        ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      trudiPartitionSum 1 (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ)

/-- There is a bijection between the non-crossing partitions of `[2n]` all of whose blocks have
even size and the Dyck paths of semilength `2n` all of whose descents (maximal runs of down steps,
read off `dyckPeakDescents`) have even length. Non-crossing partitions are the bundled
`NoncrossingPartition (2 * n)`.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 10
(`jis-2026-26.1.2-lem-10`). -/
public theorem_wanted nonempty_equiv_evenNoncrossing_evenDescentDyck (n : ℕ) :
    Nonempty
      ({P : _root_.NoncrossingPartition (2 * n) // ∀ B ∈ P.val.parts, Even B.card} ≃
        {p : DyckWord // p.semilength = 2 * n ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j})

end

end MetaMathlibExt
