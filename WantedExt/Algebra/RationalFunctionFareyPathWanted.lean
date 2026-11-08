/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.Translations
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Field.ZMod

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- The finite continued fraction `[a₀, a₁, …, aₙ]` with polynomial partial
quotients `aᵢ ∈ F[X]`, as a Mathlib generalized continued fraction over
`RatFunc F` with all partial numerators `1`. Its `nums i` and `dens i` are the
paper's partial numerators `Aᵢ` and partial denominators `Bᵢ`
(`A₋₁ = 1`, `A₀ = a₀`, `Aᵢ₊₁ = aᵢ₊₁ Aᵢ + Aᵢ₋₁`, and likewise `Bᵢ` with
`B₋₁ = 0`, `B₀ = 1`), and `convs i = Aᵢ / Bᵢ` is the `i`th convergent.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public noncomputable def polyContFract (a : ℕ → F[X]) (n : ℕ) :
    GenContFract (RatFunc F) :=
  ⟨algebraMap F[X] (RatFunc F) (a 0),
    Stream'.Seq.ofList
      ((List.range n).map fun i => ⟨1, algebraMap F[X] (RatFunc F) (a (i + 1))⟩)⟩

/-- The integral part of `polyContFract a n` is `a₀`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_h (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).h = algebraMap F[X] (RatFunc F) (a 0) := rfl

/-- The `i`th term of `polyContFract a n` is `⟨1, aᵢ₊₁⟩` for `i < n` and absent
afterwards.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_s_get? (a : ℕ → F[X]) (n i : ℕ) :
    (polyContFract a n).s.get? i =
      if i < n then some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 1))⟩ else none := by
  simp [polyContFract, Stream'.Seq.ofList_get?, List.getElem?_map]
  split_ifs <;> simp_all

/-- `A₀ = a₀`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_nums_zero (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).nums 0 = algebraMap F[X] (RatFunc F) (a 0) := by
  simp [GenContFract.zeroth_num_eq_h, polyContFract_h]

/-- `B₀ = 1`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_dens_zero (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).dens 0 = 1 := by
  simp [GenContFract.zeroth_den_eq_one]

/-- `A₁ = a₁ a₀ + 1` when `n ≥ 1`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_nums_one (a : ℕ → F[X]) {n : ℕ} (hn : 0 < n) :
    (polyContFract a n).nums 1 = algebraMap F[X] (RatFunc F) (a 1 * a 0 + 1) := by
  rw [GenContFract.first_num_eq (gp := ⟨1, algebraMap F[X] (RatFunc F) (a 1)⟩)
    (by simp [polyContFract_s_get?, hn])]
  simp [polyContFract_h]

/-- `B₁ = a₁` when `n ≥ 1`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_dens_one (a : ℕ → F[X]) {n : ℕ} (hn : 0 < n) :
    (polyContFract a n).dens 1 = algebraMap F[X] (RatFunc F) (a 1) := by
  rw [GenContFract.first_den_eq (gp := ⟨1, algebraMap F[X] (RatFunc F) (a 1)⟩)
    (by simp [polyContFract_s_get?, hn])]

/-- Theorem 4: a finite regular continued fraction `[a₀, …, aₙ]`
(`aᵢ ∈ F[X]` nonconstant for `i ≥ 1`) defines a path in the Farey graph `χ'`
over `F` from its integral part `a₀` to its value, with the convergents as
vertices: each convergent `Aᵢ / Bᵢ` is a vertex of `χ'` (`Bᵢ ≠ 0` and `Aᵢ`,
`Bᵢ` coprime), and consecutive convergents are adjacent in `χ'`
(`Aᵢ Bᵢ₋₁ - Aᵢ₋₁ Bᵢ ∈ F \ {0}`, i.e. a unit of `F[X]`).

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 4. -/
public theorem_wanted polyContFract_convergents_farey_path (a : ℕ → F[X]) (n : ℕ)
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) :
    ∃ A B : ℕ → F[X], ∀ i ≤ n,
      (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i) ∧
      (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i) ∧
      B i ≠ 0 ∧ IsCoprime (A i) (B i) ∧
      (1 ≤ i → IsUnit (A i * B (i - 1) - A (i - 1) * B i))

/-- Theorem 5: let `[a₀, …, aₙ]` (`n ≥ 1`) be a finite regular continued
fraction with partial numerators and denominators `Aᵢ`, `Bᵢ ∈ F[X]`, and let
`u / v` be adjacent to `Aₙ / Bₙ` in the Farey graph `χ'`
(`u Bₙ - v Aₙ ∈ F \ {0}`) with `deg v > deg Bₙ`. Then
`aₙ₊₁ = (v Aₙ₋₁ - u Bₙ₋₁) / (u Bₙ - v Aₙ)` is a nonconstant polynomial and the
extended path defines the continued fraction `[a₀, …, aₙ, aₙ₊₁]` of `u / v`.
Deviation: `n ≥ 1` (the case `n = 0` needs `A₋₁ = 1`, `B₋₁ = 0`); `deg vₙ` is
stated as `deg Bₙ` (they agree since `Aₙ / Bₙ = uₙ / vₙ` in lowest terms);
the membership `u / v ∈ χ'` (`u`, `v` coprime) is omitted since adjacency
implies it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 5. -/
public theorem_wanted polyContFract_extend_farey_path (a : ℕ → F[X]) {n : ℕ}
    (hn : 1 ≤ n) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree)
    (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (u v : F[X]) (hadj : IsUnit (u * B n - v * A n))
    (hdeg : (B n).degree < v.degree) :
    ∃ b : F[X], 0 < b.natDegree ∧
      algebraMap F[X] (RatFunc F) b =
        algebraMap F[X] (RatFunc F) (v * A (n - 1) - u * B (n - 1)) /
          algebraMap F[X] (RatFunc F) (u * B n - v * A n) ∧
      (polyContFract (Function.update a (n + 1) b) (n + 1)).convs (n + 1) =
        algebraMap F[X] (RatFunc F) u / algebraMap F[X] (RatFunc F) v

/-- Theorem 6: let `v₀ = 1`, `u₀ ∈ F[X]`, and for `1 ≤ i ≤ n` let
`uᵢ, vᵢ ∈ F[X]` with `deg vᵢ₋₁ < deg vᵢ` and
`uᵢ vᵢ₋₁ - uᵢ₋₁ vᵢ = cᵢ ∈ F \ {0}`. With `a₀ = u₀`, `a₁ = c₁⁻¹ v₁`,
`a₂ = -c₂⁻¹ c₁ (u₂ v₀ - u₀ v₂)` and, for `i ≥ 3`,
`aᵢ = (-1)^(i+1) cᵢ⁻¹ cᵢ₋₁ cᵢ₋₂⁻² cᵢ₋₃² ⋯ c₁^(2(-1)^i) (uᵢ vᵢ₋₂ - uᵢ₋₂ vᵢ)`,
the continued fraction `[a₀, …, aₙ]` is regular (`aᵢ` nonconstant for
`i ≥ 1`), its value is `uₙ / vₙ`, each vertex `uᵢ / vᵢ` is its `i`th
convergent, and `Aᵢ = tᵢ uᵢ`, `Bᵢ = tᵢ vᵢ` with
`tᵢ = ± cᵢ⁻¹ cᵢ₋₁ cᵢ₋₂⁻¹ cᵢ₋₃ ⋯ c₁^((-1)^i)`, sign `+` for `i ≡ 0, 1 (mod 4)`
and `-` for `i ≡ 2, 3 (mod 4)`. The paper's coprimality hypothesis
`(uᵢ, vᵢ) = 1` is omitted: it follows from the determinant condition.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6. -/
public theorem_wanted polyContFract_of_farey_path (u v : ℕ → F[X]) (c : ℕ → F) (n : ℕ)
    (hv0 : v 0 = 1) (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C (c i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = C (c 1)⁻¹ * v 1)
    (ha2 : a 2 = -C ((c 2)⁻¹ * c 1) * (u 2 * v 0 - u 0 * v 2))
    (ha : ∀ i, 3 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1) * (c i)⁻¹ * c (i - 1) *
        ∏ j ∈ Finset.Icc 1 (i - 2), c j ^ (2 * (-1 : ℤ) ^ (i - j + 1))) *
        (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, ∃ t : F,
        t = (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) *
          ∏ j ∈ Finset.Icc 1 i, c j ^ ((-1 : ℤ) ^ (i - j + 1)) ∧
        (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C t * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C t * v i) ∧
        (polyContFract a n).convs i =
          algebraMap F[X] (RatFunc F) (u i) / algebraMap F[X] (RatFunc F) (v i)

/-- Corollary 1: in the setting of Theorem 6 with `cᵢ = (-1)^(i-1)`, the path
`u₀ / v₀ → ⋯ → uₙ / vₙ` defines the regular continued fraction of `uₙ / vₙ`
with partial numerators `uᵢ`, partial denominators `vᵢ`, and partial quotients
`aᵢ = (-1)^i (uᵢ vᵢ₋₂ - uᵢ₋₂ vᵢ)` (for `i = 1`, with `u₋₁ = 1`, `v₋₁ = 0`,
this reads `a₁ = v₁`). The paper presents the corollaries for `F₂`, `F₃`; the
statement holds verbatim over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 1. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one_pow_pred
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C ((-1) ^ (i - 1)))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n → a i = C ((-1) ^ i) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (v i)

/-- Corollary 2: in the setting of Theorem 6 with `cᵢ = (-1)^i`, the path
defines the regular continued fraction of `uₙ / vₙ` with partial numerators
`(-1)^i uᵢ`, partial denominators `(-1)^i vᵢ`, and partial quotients
`a₁ = -v₁`, `aᵢ = (-1)^i (uᵢ vᵢ₋₂ - uᵢ₋₂ vᵢ)` for `i ≥ 2`. Stated over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 2. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one_pow
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C ((-1) ^ i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = -v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n → a i = C ((-1) ^ i) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C ((-1) ^ i) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C ((-1) ^ i) * v i)

/-- Corollary 3: in the setting of Theorem 6 with `cᵢ = 1`, the path defines
the regular continued fraction of `uₙ / vₙ` with partial numerators and
denominators `Aᵢ = ± uᵢ`, `Bᵢ = ± vᵢ` (sign `+` for `i ≡ 0, 1 (mod 4)`, `-` for
`i ≡ 2, 3 (mod 4)`), and partial quotients `a₁ = v₁`,
`aᵢ = (-1)^(i+1) (uᵢ vᵢ₋₂ - uᵢ₋₂ vᵢ)` for `i ≥ 2`. Stated over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 3. -/
public theorem_wanted polyContFract_of_farey_path_det_one
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = 1)
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) * v i)

/-- Corollary 4: in the setting of Theorem 6 with `cᵢ = -1`, the path defines
the regular continued fraction of `uₙ / vₙ` with partial numerators and
denominators `Aᵢ = ± uᵢ`, `Bᵢ = ± vᵢ` (sign `+` for `i ≡ 0, 3 (mod 4)`, `-` for
`i ≡ 1, 2 (mod 4)`), and partial quotients
`aᵢ = (-1)^(i+1) (uᵢ vᵢ₋₂ - uᵢ₋₂ vᵢ)` (for `i = 1`, with `u₋₁ = 1`,
`v₋₁ = 0`, this reads `a₁ = -v₁`). Stated over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 4. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = -1)
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = -v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * v i)

/-- The Farey series `𝓕ₙ` of order `n` over `F`: pairs `(u, v)` of polynomials,
read as the fraction `u / v`, with `deg u < deg v ≤ n`, `u` and `v` coprime and
`v` monic (so each fraction has exactly one such pair).

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1 (quoted from [6], there over `𝔽_{p^r}`). -/
public def polyFareySeries (n : ℕ) : Set (F[X] × F[X]) :=
  {w | w.1.degree < w.2.degree ∧ w.2.natDegree ≤ n ∧ IsCoprime w.1 w.2 ∧ w.2.Monic}

/-- The value `u / v ∈ F(x)` of a pair `(u, v)`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public noncomputable def polyFrac (w : F[X] × F[X]) : RatFunc F :=
  algebraMap F[X] (RatFunc F) w.1 / algebraMap F[X] (RatFunc F) w.2

/-- Characteristic member: `0 / 1 ∈ 𝓕ₙ` for every `n`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem zero_one_mem_polyFareySeries (n : ℕ) :
    ((0 : F[X]), (1 : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_zero_left.2 isUnit_one, monic_one⟩ <;> simp

/-- Characteristic member: `1 / x ∈ 𝓕ₙ` for `n ≥ 1`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem one_X_mem_polyFareySeries {n : ℕ} (hn : 1 ≤ n) :
    ((1 : F[X]), (X : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp [hn]

/-- `h / k` is a `deg k`-neighbour of `u / v` in `𝓕ₙ`: both fractions lie in `𝓕ₙ`,
they are distinct as rational functions,
and `|u/v - h/k| ≤ |u/v - h'/k'|` for every `h'/k' ∈ 𝓕ₙ` other than `u / v` with
`deg k' = deg k`, where `|·|` is the degree valuation (`RatFunc.inftyValuation`).
The fraction `u / v` itself is excluded from the comparison, as the paper's
counts (Theorem 3 with `t = 0`, Figure 1) require.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 2 (quoted from [6]). -/
public def IsPolyFareyDegNeighbor [DecidableEq (RatFunc F)] (n : ℕ) (w z : F[X] × F[X]) :
    Prop :=
  w ∈ polyFareySeries n ∧ z ∈ polyFareySeries n ∧ polyFrac z ≠ polyFrac w ∧
    ∀ z' ∈ polyFareySeries n, z'.2.natDegree = z.2.natDegree → polyFrac z' ≠ polyFrac w →
    RatFunc.inftyValuation F (polyFrac w - polyFrac z) ≤
      RatFunc.inftyValuation F (polyFrac w - polyFrac z')

/-- No fraction is a neighbour of itself.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 2. -/
public theorem not_isPolyFareyDegNeighbor_self [DecidableEq (RatFunc F)] (n : ℕ)
    (w : F[X] × F[X]) : ¬ IsPolyFareyDegNeighbor n w w :=
  fun h => h.2.2.1 rfl

/-- `u / v` and `h / k` in `𝓕ₙ` are neighbours: `u / v` is a `deg v`-neighbour of
`h / k` and `h / k` is a `deg k`-neighbour of `u / v`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 3 (quoted from [6]). -/
public def ArePolyFareyNeighbors [DecidableEq (RatFunc F)] (n : ℕ) (w z : F[X] × F[X]) :
    Prop :=
  IsPolyFareyDegNeighbor n z w ∧ IsPolyFareyDegNeighbor n w z

/-- Theorem 2: two fractions `u / v`, `h / k` of `𝓕ₙ` are neighbours if and only if
`deg (u k - h v) = 0`. Stated over any field (the paper, quoting [6], works over
`𝔽_{p^r}`).

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 2 (`integers-2026-A3-thm-2`). -/
public theorem_wanted arePolyFareyNeighbors_iff [DecidableEq (RatFunc F)] (n : ℕ)
    {w z : F[X] × F[X]} (hw : w ∈ polyFareySeries n) (hz : z ∈ polyFareySeries n) :
    ArePolyFareyNeighbors n w z ↔ (w.1 * z.2 - z.1 * w.2).degree = 0

/-- Theorem 3, over `𝔽_p`: if `u / v ∈ 𝓕ₙ` with `q = deg v ≥ 1`, then for every
`t ≥ 0` with `q + t ≤ n`, `u / v` has exactly `(p - 1) p^t` neighbours `h / k` with
`deg k = q + t`, and exactly one neighbour with `deg k < q`. Deviations: `t` is
restricted to `q + t ≤ n` (there are no fractions of larger degree in `𝓕ₙ`); `q ≥ 1`
is added (for `0 / 1` there is no neighbour of degree `< 0`); the field is the prime
field, the case of the paper's count `(p - 1) p^t` and of its Example 2.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 3 (`integers-2026-A3-thm-3`). -/
public theorem_wanted polyFarey_neighbor_count (p : ℕ) [Fact p.Prime]
    [DecidableEq (RatFunc (ZMod p))] (n : ℕ) {w : (ZMod p)[X] × (ZMod p)[X]}
    (hw : w ∈ polyFareySeries (F := ZMod p) n) (hq : 1 ≤ w.2.natDegree) :
    (∀ t : ℕ, w.2.natDegree + t ≤ n →
      Set.ncard {z | z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree = w.2.natDegree + t ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z} = (p - 1) * p ^ t) ∧
      ∃! z, z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree < w.2.natDegree ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z

end

end MetaMathlibExt
