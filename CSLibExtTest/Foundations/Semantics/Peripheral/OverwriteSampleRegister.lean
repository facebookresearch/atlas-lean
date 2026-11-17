/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister

namespace CSLibExtTest.Foundations.Semantics.Peripheral.OverwriteSampleRegister

/-- Reading the empty register once returns `none` and stays empty. -/
example (r : Option (ℕ × ℕ)) (s : Slot ℕ) :
    (registerLTS ℕ).MTr none [.read r] s ↔ r = none ∧ s = none :=
  registerLTS_mtr_read_empty_iff r s

/-- Overwrite: publishing `a` under ID 0 then `b` under ID 1 makes
the read return `(1, b)` and leaves the register empty. -/
example (a b : ℕ) (r : Option (ℕ × ℕ)) (s : Slot ℕ) :
    (registerLTS ℕ).MTr none [.publish 0 a, .publish 1 b, .read r] s ↔
      r = some (1, b) ∧ s = none :=
  registerLTS_mtr_publish_publish_read_iff a b r s

/-- The overwritten publication is lost: the read IDs are `[1]`
against publication IDs `[0, 1]`. -/
example (a b : ℕ) :
    readIds [Label.publish 0 a, .publish 1 b, .read (some (1, b))] = [1] ∧
      publishIds [Label.publish 0 a, .publish 1 b, .read (some (1, b))] = [0, 1] :=
  readIds_publish_publish_read a b

/-- Reads are destructive: the second read returns `none`. -/
example (n : ℕ) (v : ℕ) (r1 r2 : Option (ℕ × ℕ)) (s : Slot ℕ) :
    (registerLTS ℕ).MTr none [.publish n v, .read r1, .read r2] s ↔
      r1 = some (n, v) ∧ r2 = none ∧ s = none :=
  registerLTS_mtr_publish_read_read_iff n v r1 r2 s

/-- Publish-before-read: in the overwrite trace, the successful
read at index 2 is preceded by the publication at index 1, with no
publication in between. -/
example (a b : ℕ) :
    ∃ j, j < 2 ∧
      ([Label.publish 0 a, .publish 1 b, .read (some (1, b))] : List (Label ℕ))[j]? =
        some (.publish 1 b) ∧
      ∀ k m w, j < k → k < 2 →
        ([Label.publish 0 a, .publish 1 b, .read (some (1, b))] : List (Label ℕ))[k]? ≠
          some (.publish m w) :=
  exists_publish_index_of_read_mem
    [Label.publish 0 a, .publish 1 b, .read (some (1, b))] none
    ((registerLTS_mtr_publish_publish_read_iff a b (some (1, b)) none).mpr ⟨rfl, rfl⟩)
    2 1 b rfl

/-- Decreasing publication IDs keep the trace valid but break the
increasing-read-ID conclusion. -/
example (a b : ℕ) :
    (registerLTS ℕ).MTr none
        [.publish 1 a, .read (some (1, a)), .publish 0 b, .read (some (0, b))] none ∧
      ¬ (readIds [Label.publish 1 a, .read (some (1, a)), .publish 0 b,
          .read (some (0, b))]).Pairwise (· < ·) :=
  readIds_not_pairwise_of_decreasing_publish a b

end CSLibExtTest.Foundations.Semantics.Peripheral.OverwriteSampleRegister
