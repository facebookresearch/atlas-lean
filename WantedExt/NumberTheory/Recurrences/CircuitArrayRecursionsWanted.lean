/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic

/-!
Statements from Evans and Hendel on recursions of the rows of the circuit array: Section 3
(annihilators). A polynomial `p = ∑ aᵢ Xⁱ` acts on a sequence `G : ℕ → K` through the translation
operator `E(G_s) = G_{s+1}` as `(p(E) G)_s = ∑ aᵢ G_{s+i}`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- The operator `p(E)` annihilates `G`: `∑ᵢ (coeff p i) G_{s+i} = 0` for every `s ≥ 0`, where `E` is
the translation operator `E(G_s) = G_{s+1}`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definitions of the translation operator and of an annihilator). -/
def AnnihilatesSeq {K : Type*} [Semiring K] (p : K[X]) (G : ℕ → K) : Prop :=
  ∀ s : ℕ, p.sum (fun i a => a * G (s + i)) = 0

/-- Every operator annihilates the zero sequence.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definition of an annihilator). -/
theorem annihilatesSeq_zero {K : Type*} [Semiring K] (p : K[X]) : AnnihilatesSeq p (0 : ℕ → K) := by
  intro s
  simp [Polynomial.sum]

/-- A characteristic polynomial of a sequence annihilates it: if `G` solves the linear recurrence
`E`, then `E.charPoly` annihilates `G`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.4 (`fq-2024-hendel08232024rev2-lem-3.4`). -/
public theorem_wanted annihilatesSeq_charPoly_of_isSolution {K : Type*} [Field K]
    (E : LinearRecurrence K) (G : ℕ → K) (hG : E.IsSolution G) :
    AnnihilatesSeq E.charPoly G

/-- The Trivial Lemma, part (i): for any constant `c`, `E - c` annihilates `{cˢ}_{s ≥ 0}`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.7 (`fq-2024-hendel08232024rev2-lem-3.7`), part (i). -/
public theorem_wanted annihilatesSeq_X_sub_C_pow {K : Type*} [Field K] (c : K) :
    AnnihilatesSeq (X - C c) (fun s => c ^ s)

/-- The Addition-Multiplication Lemma: (i) if `Aᵢ` annihilates `Gᵢ` for `i` in a finite index set,
then `∏ᵢ Aᵢ` annihilates `∑ᵢ cᵢ Gᵢ` for arbitrary constants `cᵢ`; (ii) over `ℂ`, if the nonzero
characteristic polynomials `p₁, p₂` annihilate `G₁, G₂`, with roots `r₁,ⱼ` and `r₂,ⱼ'` listed with
multiplicity, then `∏_{j, j'} (E - r₁,ⱼ r₂,ⱼ')` annihilates the termwise product `G₁ G₂`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.8 (`fq-2024-hendel08232024rev2-lem-3.8`); part (ii) quoted from Jarden. -/
public theorem_wanted annihilatesSeq_sum_prod_and_mul :
    (∀ {K : Type*} [Field K] {ι : Type*} (I : Finset ι) (A : ι → K[X]) (G : ι → ℕ → K)
        (c : ι → K), (∀ i ∈ I, AnnihilatesSeq (A i) (G i)) →
        AnnihilatesSeq (∏ i ∈ I, A i) (fun s => ∑ i ∈ I, c i * G i s)) ∧
      ∀ (p₁ p₂ : ℂ[X]) (G₁ G₂ : ℕ → ℂ), p₁ ≠ 0 → p₂ ≠ 0 →
        AnnihilatesSeq p₁ G₁ → AnnihilatesSeq p₂ G₂ →
        AnnihilatesSeq ((p₁.roots ×ˢ p₂.roots).map (fun r => X - C (r.1 * r.2))).prod
          (fun s => G₁ s * G₂ s)

/-! ### Section 2: the circuit array

The circuit array is read off a triangular grid of resistances that is reduced one row at a time
(Steps 1-5 of Section 2: a `Δ`-`Y` transformation on every upright triangle, series on the boundary,
`Y`-`Δ` on the remaining out-stars). A labelling of a grid is a function `T r d e`, the resistance of
edge `e` of the upright triangle in row `r` (from the top) and diagonal `d` (from the left), with
`1 ≤ d ≤ r`. The grid here has no bottom row: the paper reads the circuit array off an all-one
`n`-grid with `n ≥ 4j - 2`, whose bottom edges never reach the entries in column `j`. Values at
indices outside `1 ≤ d ≤ r` are junk. -/

/-- The three edges of an upright triangle: left, right and base.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (edge labels `L`, `R`, `B`). -/
inductive CircuitEdge
  | left
  | right
  | base

/-- The `Δ`-`Y` resistance function `Δ(x, y, z) = xy / (x + y + z)`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.1). -/
def circuitDelta {K : Type*} [Field K] (x y z : K) : K :=
  x * y / (x + y + z)

/-- The `Y`-`Δ` resistance function `Y(a, b, c) = (ab + bc + ca) / a`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.1). -/
def circuitY {K : Type*} [Field K] (a b c : K) : K :=
  (a * b + b * c + c * a) / a

/-- The `Δ`-`Y` arm from the centre of an upright triangle to its top vertex, `Δ(L, R, B)`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₁₂ = Δ(L, R, B)`). -/
def circuitTopArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .left) (t .right) (t .base)

/-- The `Δ`-`Y` arm from the centre of an upright triangle to its bottom-right vertex,
`Δ(R, B, L)`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₄ = Δ(R, B, L)`). -/
def circuitRightArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .right) (t .base) (t .left)

/-- The `Δ`-`Y` arm from the centre of an upright triangle to its bottom-left vertex,
`Δ(B, L, R)`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Figure 2 (`Y₈ = Δ(B, L, R)`). -/
def circuitLeftArm {K : Type*} [Field K] (t : CircuitEdge → K) : K :=
  circuitDelta (t .base) (t .left) (t .right)

/-- The left-perimeter function `𝒫(T_{r,1}, T_{r+1,1})`: series of the bottom-left arm of
`T_{r,1}` and the top arm of `T_{r+1,1}`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.2). -/
def circuitPerimeter {K : Type*} [Field K] (t u : CircuitEdge → K) : K :=
  circuitLeftArm t + circuitTopArm u

/-- The non-boundary left-edge function `ℒ(T_{r,d-1}, T_{r,d}, T_{r+1,d})`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.5). -/
def circuitLeftEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitRightArm t) (circuitLeftArm u) (circuitTopArm v)

/-- The right-edge function `ℛ(T_{r,d}, T_{r,d+1}, T_{r+1,d+1})`: `Y`-`Δ` of the out-star at the
bottom-right vertex of `T_{r,d}`, with the arm of `T_{r,d+1}` (the one opposite the new edge) first.
This follows Steps 2-5 and Figure 2; the displayed equation (2.4) instead lists `T_{r+1,d}` and puts
the arm of `T_{r,d}` first, which gives `C₁,₂ = 29/36` against Table 1's `13/12`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.4) (corrected as above). -/
def circuitRightEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitLeftArm u) (circuitRightArm t) (circuitTopArm v)

/-- The base-edge function `ℬ(T_{r+2,d+1}, T_{r+1,d}, T_{r+1,d+1})`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
equation (2.3). -/
def circuitBaseEdge {K : Type*} [Field K] (t u v : CircuitEdge → K) : K :=
  circuitY (circuitTopArm t) (circuitRightArm u) (circuitLeftArm v)

/-- One row reduction of a labelled triangular grid: left boundary edges by `𝒫`, other left edges
by `ℒ`, right boundary edges (`d = r`) by the mirror-image series, other right edges by `ℛ`, base
edges by `ℬ`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (row reduction, equations (2.2)-(2.5)). -/
def circuitReduce {K : Type*} [Field K] (T : ℕ → ℕ → CircuitEdge → K) :
    ℕ → ℕ → CircuitEdge → K
  | r, d, .left =>
      if d = 1 then circuitPerimeter (T r 1) (T (r + 1) 1)
      else circuitLeftEdge (T r (d - 1)) (T r d) (T (r + 1) d)
  | r, d, .right =>
      if d = r then circuitRightArm (T r r) + circuitTopArm (T (r + 1) (r + 1))
      else circuitRightEdge (T r d) (T r (d + 1)) (T (r + 1) (d + 1))
  | r, d, .base => circuitBaseEdge (T (r + 2) (d + 1)) (T (r + 1) d) (T (r + 1) (d + 1))

/-- The all-one grid reduced `m` times, where after the `m`-th reduction every boundary edge
(left edges on diagonal `1`, right edges on diagonal `r`) is replaced by `bdry m` when that is
`some x`. With `bdry = none` this is the numerical reduction; Definitions 2.4 and 2.5 replace
boundary values by variables.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 2 (reductions `T^m`, Definitions 2.4 and 2.5). -/
def circuitGrid {K : Type*} [Field K] (bdry : ℕ → Option K) : ℕ → ℕ → ℕ → CircuitEdge → K
  | 0 => fun _ _ _ => 1
  | m + 1 => fun r d e =>
      match e with
      | .left =>
          if d = 1 then (bdry (m + 1)).getD (circuitReduce (circuitGrid bdry m) r d .left)
          else circuitReduce (circuitGrid bdry m) r d .left
      | .right =>
          if d = r then (bdry (m + 1)).getD (circuitReduce (circuitGrid bdry m) r d .right)
          else circuitReduce (circuitGrid bdry m) r d .right
      | .base => circuitReduce (circuitGrid bdry m) r d .base

/-- The circuit array of a grid family: `C_{i,j} = T^j_{2j-1, j - ⌊(i+1)/2⌋, L}` for even `i` and
the right edge for odd `i`, meaningful for `0 ≤ i ≤ 2(j - 1)`, `j ≥ 1`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.3. -/
def circuitArrayOf {K : Type*} [Field K] (bdry : ℕ → Option K) (i j : ℕ) : K :=
  circuitGrid bdry j (2 * j - 1) (j - (i + 1) / 2) (if Even i then .left else .right)

/-- The numerical circuit array `C_{i,j}` (Table 1), from the all-one grid.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.3 and Table 1. -/
def circuitArray (i j : ℕ) : ℚ :=
  circuitArrayOf (fun _ => none) i j

/-- The one-variable circuit array `C^X_{i,j}` (Table 2): the boundary value `2/3` of the
once-reduced grid is replaced by `(X - 3)/X`, and the reductions continue.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.4 and Table 2. -/
noncomputable def circuitArrayX (i j : ℕ) : RatFunc ℚ :=
  circuitArrayOf (fun m => if m = 1 then some ((RatFunc.X - 3) / RatFunc.X) else none) i j

/-- The variable `X_m` in the field of rational functions in `X₀, X₁, …` over `ℚ`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 (the variables `X_i`). -/
noncomputable def circuitVar (m : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ)) (MvPolynomial.X m)

/-- The multivariable circuit array `C^M_{i,j}` (Table 3): after the `m`-th reduction, `m ≥ 1`,
the boundary edges are set to the variable `X_m`, so that `C^M_{2(m-1),m} = X_m`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 and Table 3. -/
noncomputable def circuitArrayM (i j : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  circuitArrayOf (fun m => if m = 0 then none else some (circuitVar m)) i j

/-- Table 1, first entries: `C₀,₁ = 2/3`, `C₀,₂ = 26/27`, `C₁,₂ = 13/12`, `C₂,₂ = 1/2`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Table 1. -/
theorem circuitArray_small :
    circuitArray 0 1 = 2 / 3 ∧ circuitArray 0 2 = 26 / 27 ∧ circuitArray 1 2 = 13 / 12 ∧
      circuitArray 2 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [circuitArray, circuitArrayOf, circuitGrid, circuitReduce, circuitPerimeter,
      circuitLeftEdge, circuitRightEdge, circuitBaseEdge, circuitTopArm, circuitRightArm,
      circuitLeftArm, circuitDelta, circuitY]

/-- Proposition 4.1 (iv): `C^X₀,₁ = (X - 3)/X`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.4 and Proposition 4.1 (iv). -/
theorem circuitArrayX_zero_one : circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X := by
  simp [circuitArrayX, circuitArrayOf, circuitGrid]

/-- The left-side diagonal of `C^M`: `C^M₀,₁ = X₁` and `C^M₂,₂ = X₂`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5. -/
theorem circuitArrayM_diagonal :
    circuitArrayM 0 1 = circuitVar 1 ∧ circuitArrayM 2 2 = circuitVar 2 := by
  constructor <;> simp [circuitArrayM, circuitArrayOf, circuitGrid]

/-! ### Section 4 -/

/-- Proposition 4.1 (i)-(iv): rows of `C^X` from the previous column, with `C^X_{i,j} = 1` for
`i < 0` (Part (v)). Each triangle argument is `(C_{i,j}, C_{i-1,j}, C_{i-1,j})` (left, right, base).
`ℛ` is `circuitRightEdge`, the right-edge function of the reduction algorithm (the displayed (2.4)
is misprinted, see `circuitRightEdge`); with it, the argument lists of (i)-(iii) are as printed,
reading `C_{2(c-1-4),j-1}` in (iii) as `C_{2(c-1)-4,j-1}`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Proposition 4.1 (`fq-2024-hendel08232024rev2-prop-4.1`). -/
public theorem_wanted circuitArrayX_inductive :
    let C : ℤ → ℕ → RatFunc ℚ := fun i j => if i < 0 then 1 else circuitArrayX i.toNat j
    let tri : ℤ → ℕ → CircuitEdge → RatFunc ℚ := fun i j e =>
      match e with
      | .left => C i j
      | .right => C (i - 1) j
      | .base => C (i - 1) j
    (∀ c : ℕ, 2 ≤ c →
        C (2 * ((c : ℤ) - 1)) c = circuitPerimeter (tri (2 * ((c : ℤ) - 2)) (c - 1))
          (tri (2 * ((c : ℤ) - 2)) (c - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c < j →
        C (2 * ((c : ℤ) - 1)) j = circuitLeftEdge (tri (2 * ((c : ℤ) - 1)) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 2) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c ≤ j →
        C (2 * ((c : ℤ) - 1) - 1) j = circuitRightEdge (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 4) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 4) (j - 1))) ∧
      circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X

/-- Corollary 4.4: the closed form (2.6) of row `0`, `C^X₀,ₛ = (3·9^{s-2}X - 1)/(3·9^{s-2}X)` for
`s ≥ 1` (Table 2, row `0`), and numerically `C₀,ₛ = (9^s/3 - 1)/(9^s/3)`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.4 (`fq-2024-hendel08232024rev2-cor-4.4`) with (2.6). -/
public theorem_wanted circuitArrayX_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayX 0 s = (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X) ∧
      circuitArray 0 s = ((9 : ℚ) ^ s / 3 - 1) / ((9 : ℚ) ^ s / 3)

/-- Corollary 4.5, corrected: `C^X₁,ₛ = (3·9^{s-2}X - 1)/(3·9^{s-2}X - 3)` for `s ≥ 2`. The printed
denominator `3·9^{s-2}X` is the row-`0` formula; Table 2 has `(3X - 1)/(3X - 3)` at `s = 2`
(`13/12` at `X = 9`, not `26/27`).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.5 (`fq-2024-hendel08232024rev2-cor-4.5`), denominator corrected from Table 2. -/
public theorem_wanted circuitArrayX_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 1 s =
      (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 3)

/-- Corollary 4.6: for `s ≥ 2`, `C^X₂,ₛ = (c₂,₀(s) - c₂,₁(s) X + c₂,₂(s) X²)/(9^{s-2}X - 1)²` with
`c₂,₀(s) = 27·9^{s-3} - 1`, `c₂,₁(s) = 24(2s - 3)·9^{s-3}`, `c₂,₂(s) = 81·81^{s-3} - 3·9^{s-3}`
(reading the printed `c₂,₂(X²)` as `c₂,₂(s)X²`, as in Remark 4.7).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.6 (`fq-2024-hendel08232024rev2-cor-4.6`). -/
public theorem_wanted circuitArrayX_row_two (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 2 s =
      ((27 * 9 ^ ((s : ℤ) - 3) - 1) - 24 * (2 * (s : RatFunc ℚ) - 3) * 9 ^ ((s : ℤ) - 3) * RatFunc.X +
          (81 * 81 ^ ((s : ℤ) - 3) - 3 * 9 ^ ((s : ℤ) - 3)) * RatFunc.X ^ 2) /
        (9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) ^ 2

/-- Corollary 4.8: `C^M₀,ₛ = (9^{s-1} - 1 + X₁)/9^{s-1}` for `s ≥ 1`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.8 (`fq-2024-hendel08232024rev2-cor-4.8`). -/
public theorem_wanted circuitArrayM_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayM 0 s = (9 ^ (s - 1) - 1 + circuitVar 1) / 9 ^ (s - 1)

/-- Corollary 4.10: `C^M₁,ₛ = (9^{s-1} - 1 + X₁)/(3(X₁ + 3·9^{s-2} - 1))` for `s ≥ 2`.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.10 (`fq-2024-hendel08232024rev2-cor-4.10`). -/
public theorem_wanted circuitArrayM_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayM 1 s = (9 ^ (s - 1) - 1 + circuitVar 1) / (3 * (circuitVar 1 + 3 * 9 ^ (s - 2) - 1))

/-- Corollary 4.12: for `s ≥ 2`,
`C^M₂,ₛ = (Σ_{i,j} c_{i,j}(s) X₁ⁱ X₂ʲ)/(3·9^{s-2} - 1 + X₁)²` with `c₂,₁ = 9^{s-2}`,
`c₂,₀ = 9^{s-2} - 1`, `c₁,₁ = 4·9^{s-2}`, `c₁,₀ = 2 + (16(s-2) - 2)9^{s-2}`, `c₀,₁ = 4·9^{s-2}`,
`c₀,₀ = -1 + 9·81^{s-2} - (8 + 16(s-2))9^{s-2}`, and the annihilators of Table 4 for the coefficient
sequences `s ↦ c_{i,j}(s + 2)`: `(E-81)(E-9)²(E-1)`, `(E-1)(E-9)`, `(E-9)²(E-1)`, `E-9`,
`(E-1)(E-9)`, `E-9` for `c₀,₀, c₀,₁, c₁,₀, c₁,₁, c₂,₀, c₂,₁`. The paper's base case is `s = 3`; the
identity also holds at `s = 2`. The recursions column of Table 4 is omitted (its `X₁⁰X₂¹` entry
`G_s = 10G_{s-1} - G_{s-2}` is misprinted for `- 9G_{s-2}`).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.12 (`fq-2024-hendel08232024rev2-cor-4.12`) and Table 4. -/
public theorem_wanted circuitArrayM_row_two :
    (∀ s : ℕ, 2 ≤ s →
      circuitArrayM 2 s =
        (9 ^ (s - 2) * circuitVar 1 ^ 2 * circuitVar 2 + (9 ^ (s - 2) - 1) * circuitVar 1 ^ 2 +
            4 * 9 ^ (s - 2) * circuitVar 1 * circuitVar 2 +
            (2 + (16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2) - 2) * 9 ^ (s - 2)) * circuitVar 1 +
            4 * 9 ^ (s - 2) * circuitVar 2 +
            (-1 + 9 * 81 ^ (s - 2) - (8 + 16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2)) * 9 ^ (s - 2))) /
          (3 * 9 ^ (s - 2) - 1 + circuitVar 1) ^ 2) ∧
      AnnihilatesSeq ((X - C 81) * (X - C 9) ^ 2 * (X - C 1))
        (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 9) ^ 2 * (X - C 1)) (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => (9 : ℚ) ^ s - 1) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => (9 : ℚ) ^ s)

end

end MetaMathlibExt
