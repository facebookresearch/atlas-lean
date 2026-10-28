/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsWordChain

/-! Phase-correct finite Q images of genuine chronological local fiber chains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A chronological chain of complete Q images accumulates each new action on the left. -/
def generatedAxisGlobalQImageChain (f : ℕ → Q → Q) : ℕ → Q → Q
  | 0, q => q
  | n + 1, q => f n (generatedAxisGlobalQImageChain f n q)

/-- Genuine stage conjugations determine the whole fiber-chain image with every central phase. -/
theorem generatedAxisGlobalQImageChain_actual (e : ℕ → localFiberSubgroup)
    (f : ℕ → Q → Q) (hf : ∀ j q, spinConjugation (e j).val.1 q = f j q)
    (n : ℕ) (q : Q) :
    spinConjugation (generatedAxisGlobalWordChain e n).val.1 q =
      generatedAxisGlobalQImageChain f n q := by
  induction n with
  | zero =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | succ n ih =>
    change spinConjugation ((e n).val.1 *
      (generatedAxisGlobalWordChain e n).val.1) q = _
    rw [map_mul]
    change spinConjugation (e n).val.1
      (spinConjugation (generatedAxisGlobalWordChain e n).val.1 q) = _
    rw [ih, hf]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
