/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import MathlibExt.NumberTheory.PrimeGapLiminf
public import WantedExt.NumberTheory.PrimeGapBoundsHypotheses

/-!
# Bounded prime-gap literature requests

The chronological catalogue upper rows and the three conditional bounds are
private unproved data. The external PrimeGaps186 development is not imported.
Its three declared analytic/numerical inputs do not become axioms of this library.
Source: Optimization Problems, constants/88a.md, revision
2c1968cd520b60f1cf3cf50749f7285e800e4e15. See Sources/PrimeGapBounds.md for gaps.
-/

@[expose] public section

namespace WantedExt.NumberTheory.PrimeGapBounds

open MathlibExt.NumberTheory

/-- Zhang's first explicit consecutive-prime-gap bound.
Source: Zhang, Annals of Mathematics 179 (2014), 1121-1174; Polymath8b v4, Theorem 1.2. -/
theorem_wanted zhang2014UpperBound : primeGapLiminf ≤ (70000000 : WithTop ℕ)

/-- The separately attributed Polymath8a improvement.
Source: Polymath, Algebra & Number Theory 8 (2014), 2067-2199; Polymath8b v4, Introduction. -/
theorem_wanted polymath8a2014UpperBound : primeGapLiminf ≤ (4680 : WithTop ℕ)

/-- Maynard's unconditional bound, also obtained independently by Tao.
Source: Maynard, Annals of Mathematics 181 (2015), 383-413; Polymath8b v4, Theorem 1.3(i). -/
theorem_wanted maynard2015UpperBound : primeGapLiminf ≤ (600 : WithTop ℕ)

/-- The Polymath8b bound from the retained original v4; erratum applicability is unresolved.
Source: Polymath8b, arXiv:1407.4897v4, Theorem 1.4(i), DOI 10.1186/s40687-014-0012-7. -/
theorem_wanted polymath8b2014UpperBound : primeGapLiminf ≤ (246 : WithTop ℕ)

/-- The first 2026 bound 240, retaining its distinct author and date.
Source: Zhang, Zenodo 10.5281/zenodo.22135842, 28 August 2026, as quoted in constants/88a.md. -/
theorem_wanted zhang2026UpperBound : primeGapLiminf ≤ (240 : WithTop ℕ)

/-- The quoted 186 bound; its external analytic and numerical inputs are not assumed here.
Source: OpenAI, Improved short gaps between primes, 30 August 2026, quoted in constants/88a.md. -/
theorem_wanted openai2026UpperBound : primeGapLiminf ≤ (186 : WithTop ℕ)

/-- The independent second 2026 bound 240, not identified with Zhang's provenance.
Source: Stadlmann, arXiv:2608.31126, 31 August 2026, as quoted in constants/88a.md. -/
theorem_wanted stadlmann2026UpperBound : primeGapLiminf ≤ (240 : WithTop ℕ)

/-- Maynard's bound under the actual dyadic Elliott-Halberstam assumption.
Source: Maynard (2015); Polymath8b v4, Theorem 1.3(iii). -/
theorem_wanted maynardElliottHalberstamUpperBound :
  Polymath8b.ElliottHalberstam → primeGapLiminf ≤ (12 : WithTop ℕ)

/-- GPY's older, separately recorded conditional bound.
Source: Goldston-Pintz-Yıldırım (2009); Polymath8b v4, Theorem 1.1. -/
theorem_wanted gpyElliottHalberstamUpperBound :
  Polymath8b.ElliottHalberstam → primeGapLiminf ≤ (16 : WithTop ℕ)

/-- The GEH bound from the retained original v4, not an assumed theorem.
Source: Polymath8b v4, Theorem 1.4(xii); the 2015 erratum correction is unavailable. -/
theorem_wanted polymath8bGeneralizedElliottHalberstamUpperBound :
  Polymath8b.GeneralizedElliottHalberstam → primeGapLiminf ≤ (6 : WithTop ℕ)

/-- The source's DHL[40,2] claim for actual distinct admissible integer tuples.
`Int.toNat.Prime` counts positive primes and excludes negative integers and zero.
Source: OpenAI (2026), Theorem 1.1, as quoted in the 186 row of constants/88a.md. -/
theorem_wanted openai2026DHL :
  ∀ h : Fin 40 → ℤ, Function.Injective h →
    MetaMathlibExt.IsHardyLittlewoodAdmissible 40 h →
      Set.Infinite {n : ℕ |
        2 ≤ (Finset.univ.filter (fun i : Fin 40 ↦ Nat.Prime ((n : ℤ) + h i).toNat)).card}

/-- All forty shifts of the explicit source tuple, including both endpoints.
Source: OpenAI (2026), equation (1.3), retained PrimeGaps186.lean lines 1095-1104. -/
def shifts186 : List ℤ :=
  [0, 2, 6, 12, 20, 26, 30, 32, 36, 42, 48, 50, 56, 60, 68, 72, 78, 86, 90, 92,
    98, 102, 110, 116, 120, 126, 132, 138, 140, 146, 152, 156, 158, 162,
    168, 170, 176, 180, 182, 186]

/-- The explicit tuple uses the existing integer-valued prime-tuple API.
Source: OpenAI (2026), equation (1.3), and the 186 row of constants/88a.md. -/
def tuple186 (i : Fin 40) : ℤ := shifts186.get ⟨i.val, by simp [shifts186]⟩

/-- The forty displayed entries are distinct.
Source: the explicit tuple in OpenAI (2026), equation (1.3). -/
theorem tuple186_injective : Function.Injective tuple186 := by decide

/-- Every displayed entry is between the two source endpoints.
Source: the explicit tuple in OpenAI (2026), equation (1.3). -/
theorem tuple186_bounds : ∀ i : Fin 40, 0 ≤ tuple186 i ∧ tuple186 i ≤ 186 := by decide

/-- The actual finite set of displayed integer shifts has diameter 186.
Source: OpenAI (2026), equation (1.3), as quoted in constants/88a.md. -/
theorem tuple186_diameter :
    (Finset.univ.image tuple186).max' (by simp) -
      (Finset.univ.image tuple186).min' (by simp) = 186 := by
  let s := Finset.univ.image tuple186
  have hs : s.Nonempty := by simp [s]
  have hmax : s.max' hs = 186 := by
    apply (Finset.max'_eq_iff s hs 186).2
    constructor
    · exact Finset.mem_image.mpr ⟨39, Finset.mem_univ _, rfl⟩
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
      exact (tuple186_bounds i).2
  have hmin : s.min' hs = 0 := by
    apply (Finset.min'_eq_iff s hs 0).2
    constructor
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
      exact (tuple186_bounds i).1
  change s.max' hs - s.min' hs = 186
  rw [hmax, hmin]
  norm_num

/-- The explicit tuple is admissible in the existing Hardy-Littlewood sense.
Source: OpenAI (2026), equation (1.3); retained PrimeGaps186.lean lines 1109-1117. -/
theorem tuple186_admissible : MetaMathlibExt.IsHardyLittlewoodAdmissible 40 tuple186 := by
  intro p hp
  by_cases h : p < 41
  · have small : ∀ q ∈ Finset.range 41, Nat.Prime q →
        MetaMathlibExt.hardyLittlewoodResidueCount 40 tuple186 q ≠ q := by decide +kernel
    exact small p (Finset.mem_range.mpr h) hp
  · have hcard : MetaMathlibExt.hardyLittlewoodResidueCount 40 tuple186 p ≤ 40 := by
      unfold MetaMathlibExt.hardyLittlewoodResidueCount
      exact Finset.card_image_le.trans (by simp)
    exact ne_of_lt (hcard.trans_lt (by omega))

end WantedExt.NumberTheory.PrimeGapBounds
