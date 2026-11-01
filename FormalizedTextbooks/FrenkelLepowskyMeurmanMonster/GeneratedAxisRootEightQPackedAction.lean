/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitiveAction
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedActions

/-! Bounded packed evaluations retain the entire actual root-eight extraspecial action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact binary and central obligations for one full original primitive action. -/
def generatedRootEightQPackedCondition (k : Fin 11) (input output : ℕ) : Prop :=
  generatedAxisGlobalQMaskVector (generatedRootEightQPrimitiveColumns k)
      (generatedNinthLowerSpinPrimitivePackedBinary input) =
    generatedNinthLowerSpinPrimitivePackedBinary output ∧
  generatedNinthLowerSpinPrimitivePackedCentral input +
    (if (generatedAxisGlobalQMaskCentral (generatedRootEightQPrimitiveRows k)
      (generatedRootEightQPrimitiveCoefficients k)
      (generatedNinthLowerSpinPrimitivePackedBinary input)).testBit 0
      then (1 : ZMod 2) else 0) = generatedNinthLowerSpinPrimitivePackedCentral output

/-- A packed primitive certificate proves the full actual Q image, including central signs. -/
theorem generatedRootEight_Q_packed_actual (k : Fin 11) (input output : ℕ)
    (h : generatedRootEightQPackedCondition k input output) :
    generatedRootEightQPrimitiveImage k (generatedNinthLowerSpinPrimitivePackedQ input) =
      generatedNinthLowerSpinPrimitivePackedQ output := by
  rw [← generatedRootEight_Q_primitive_image,
    generatedNinth_lower_spin_primitive_packed_normal_form, map_mul,
    spinConjugation_central, generatedRootEight_Q_primitive_mask_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    have hb := congrArg (monsterCo1GeometryBinaryMaskDecode (n := 24)) h.1
    simpa only [generatedAxisGlobalQMaskImage, generatedNinthLowerSpinPrimitivePackedQ,
      toAdd_ofAdd, generatedNinth_lower_spin_primitive_packed_label_decode] using
      hb.trans (generatedAxisGlobalSourceMaskJoin_decode
        (output % 4096) ((output / 4096) % 4096))
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    exact h.2

/-- Ordinary product-order words keep every original Q primitive phase. -/
def generatedRootEightQWordImage (w : List (Fin 11)) (q : Q) : Q :=
  w.foldr generatedRootEightQPrimitiveImage q

/-- The word evaluator is the full conjugation by its actual product of source fibers. -/
theorem generatedRootEight_Q_word_actual (w : List (Fin 11)) (q : Q) :
    spinConjugation ((w.map generatedRootEightQPrimitiveFiber).prod).val.1 q =
      generatedRootEightQWordImage w q := by
  induction w with
  | nil =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | cons k w ih =>
    change spinConjugation
      ((generatedRootEightQPrimitiveFiber k).val.1 *
        ((w.map generatedRootEightQPrimitiveFiber).prod).val.1) q = _
    rw [map_mul]
    change spinConjugation (generatedRootEightQPrimitiveFiber k).val.1
      (spinConjugation ((w.map generatedRootEightQPrimitiveFiber).prod).val.1 q) = _
    rw [ih, generatedRootEight_Q_primitive_image]
    rfl

/-- Certified literal prefixes replay the complete original word with every central phase. -/
theorem generatedRootEight_Q_word_replay (w : List (Fin 11)) (cache : ℕ → ℕ)
    (q : Q) (hbase : generatedNinthLowerSpinPrimitivePackedQ (cache 0) = q)
    (hsteps : ∀ n (hn : n < w.reverse.length),
      generatedRootEightQPackedCondition w.reverse[n] (cache n) (cache (n + 1))) :
    generatedRootEightQWordImage w q =
      generatedNinthLowerSpinPrimitivePackedQ (cache w.length) := by
  have hp : ∀ n, n ≤ w.reverse.length →
      (w.reverse.take n).foldl (fun a k => generatedRootEightQPrimitiveImage k a) q =
        generatedNinthLowerSpinPrimitivePackedQ (cache n) := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact hbase.symm
    | succ n ih =>
      intro hn
      have hnl : n < w.reverse.length := by omega
      rw [List.take_succ_eq_append_getElem hnl, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      exact generatedRootEight_Q_packed_actual _ _ _ (hsteps n hnl)
  rw [generatedRootEightQWordImage, List.foldr_eq_foldl_reverse]
  have hf := hp w.reverse.length (Nat.le_refl _)
  rw [List.take_length, List.length_reverse] at hf
  exact hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
