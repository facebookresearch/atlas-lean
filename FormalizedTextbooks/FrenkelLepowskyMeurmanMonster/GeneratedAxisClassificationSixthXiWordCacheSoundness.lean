/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCache15

/-! All bounded C-model checks give exact signed operator equality on every integer spin vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every C and inverse-C cache entry equals its complete original signed spin model. -/
theorem generatedSixth_xi_word_cache (k : Fin 2) (n : Fin 4096) :
    generatedSixthXiWordCachedLabel k n =
      generatedSixthMonomialMaskLabel (generatedSixthXiWordCoordinateRows k) n.val ∧
    generatedSixthXiWordCachedPhase k n =
      (if (generatedSixthMonomialMaskQuadratic
        (fun i => (generatedSixthXiWordPhaseRows k i).val) n.val).testBit 0 then 1 else 0) := by
  have h : ∀ b : Fin 16, ∀ a : Fin 256,
      let t : Fin 4096 := ⟨b.val * 256 + a.val, by omega⟩
      generatedSixthXiWordCachedLabel k t =
        generatedSixthMonomialMaskLabel (generatedSixthXiWordCoordinateRows k) t.val ∧
      generatedSixthXiWordCachedPhase k t =
        (if (generatedSixthMonomialMaskQuadratic
          (fun i => (generatedSixthXiWordPhaseRows k i).val) t.val).testBit 0 then 1 else 0) := by
    intro b a
    fin_cases b
    · exact generatedSixth_xi_word_cache00 k a
    · exact generatedSixth_xi_word_cache01 k a
    · exact generatedSixth_xi_word_cache02 k a
    · exact generatedSixth_xi_word_cache03 k a
    · exact generatedSixth_xi_word_cache04 k a
    · exact generatedSixth_xi_word_cache05 k a
    · exact generatedSixth_xi_word_cache06 k a
    · exact generatedSixth_xi_word_cache07 k a
    · exact generatedSixth_xi_word_cache08 k a
    · exact generatedSixth_xi_word_cache09 k a
    · exact generatedSixth_xi_word_cache10 k a
    · exact generatedSixth_xi_word_cache11 k a
    · exact generatedSixth_xi_word_cache12 k a
    · exact generatedSixth_xi_word_cache13 k a
    · exact generatedSixth_xi_word_cache14 k a
    · exact generatedSixth_xi_word_cache15 k a
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let a : Fin 256 := ⟨n.val % 256, by omega⟩
  have he : (⟨b.val * 256 + a.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, a]
    omega
  have hh := h b a
  have hv : b.val * 256 + a.val = n.val := congrArg Fin.val he
  simpa only [he, hv] using hh

/-- The cached C signed pullback for arbitrary actual integer spin vectors. -/
def generatedSixthXiWordCachedInteger (k : Fin 2) (v : NortonUIntegerVector)
    (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (generatedSixthXiWordCachedPhase k n) *
    v (generatedSixthXiWordCachedLabel k n)

/-- Complete cached signed pullback is the original C operator on every integer vector. -/
theorem generatedSixth_xi_word_cached_integer (k : Fin 2) (v : NortonUIntegerVector) :
    generatedSixthXiWordCachedInteger k v =
      generatedSixthSpinMaskInteger (generatedSixthXiWordCoordinateRows k)
        (generatedSixthXiWordPhaseRows k) v := by
  funext n
  rw [generatedSixthXiWordCachedInteger, (generatedSixth_xi_word_cache k n).1,
    (generatedSixth_xi_word_cache k n).2]
  rfl

/-- The two full original C models surround all 64 unchanged Gaussian terms. -/
def generatedSixthXiCachedSpinInteger (v : NortonUIntegerVector) : NortonUIntegerVector :=
  generatedSixthXiWordCachedInteger 1
    (generatedSixthIntegerXiCached (generatedSixthXiWordCachedInteger 0 v))

/-- Both complete C caches give exactly the original conjugated Xi integer operator. -/
theorem generatedSixth_xi_cached_spin_integer (v : NortonUIntegerVector) :
    generatedSixthXiCachedSpinInteger v = generatedSixthXiFastSpinInteger v := by
  rw [generatedSixthXiCachedSpinInteger, generatedSixth_xi_word_cached_integer,
    generatedSixth_xi_word_cached_integer]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
