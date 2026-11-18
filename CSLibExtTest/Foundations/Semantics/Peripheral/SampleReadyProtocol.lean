/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.SampleReadyProtocol

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol

namespace CSLibExtTest.Foundations.Semantics.Peripheral.SampleReadyProtocol

/-- Headline correctness on a concrete trace: publishing `a` under
ID 0, polling, reading and delivering delivers `(0, a)`, fed by the
read at index 2 and the publication at index 0, with no other
publication in between. -/
example (a : ℕ) :
    ∃ j k, k < j ∧ j < 3 ∧
      ([DriverLabel.env (.publish 0 a), .poll true, .read (some (0, a)),
        .deliver 0 a] : List (DriverLabel ℕ))[j]? = some (.read (some (0, a))) ∧
      (∀ l, j < l → l < 3 →
        ∃ μ, ([DriverLabel.env (.publish 0 a), .poll true, .read (some (0, a)),
          .deliver 0 a] : List (DriverLabel ℕ))[l]? = some (.env μ)) ∧
      ([DriverLabel.env (.publish 0 a), .poll true, .read (some (0, a)),
        .deliver 0 a] : List (DriverLabel ℕ))[k]? = some (.env (.publish 0 a)) ∧
      ∀ l m w, k < l → l < j →
        ([DriverLabel.env (.publish 0 a), .poll true, .read (some (0, a)),
          .deliver 0 a] : List (DriverLabel ℕ))[l]? ≠ some (.env (.publish m w)) :=
  deliver_correct
    [DriverLabel.env (.publish 0 a), .poll true, .read (some (0, a)), .deliver 0 a]
    (.idle, none)
    (.stepL (.env _ (.publish _ _ _)) (.stepL (.poll _)
      (.stepL (.read (.read _)) (.stepL (.deliver _ _ _) .refl))))
    3 0 a rfl

/-- Publish between Ready and Read: after publishing `a` under ID 0,
polling, then publishing `c` under ID 1, the read returns the newer
`(1, c)` and that is the only sample delivered. -/
example (a c : ℕ) (b : Bool) (r : Option (ℕ × ℕ)) (n : ℕ) (w : ℕ)
    (x : Phase ℕ × Slot ℕ) :
    (driverLTS ℕ).MTr (.idle, none)
        [.env (.publish 0 a), .poll b, .env (.publish 1 c), .read r, .deliver n w] x ↔
      b = true ∧ r = some (1, c) ∧ n = 1 ∧ w = c ∧ x = (.idle, none) :=
  driverLTS_mtr_publish_between_poll_and_read_iff a c b r n w x

/-- An interleaving clear makes the read empty: after publishing
`a` under ID 0 and polling, another reader clears the slot; the
driver had observed Ready = `true`, its read returns `none`, and
it retries. -/
example (a : ℕ) (b : Bool) (r₀ r : Option (ℕ × ℕ)) (x : Phase ℕ × Slot ℕ) :
    (driverLTS ℕ).MTr (.idle, none)
        [.env (.publish 0 a), .poll b, .env (.read r₀), .read r, .retry] x ↔
      b = true ∧ r₀ = some (0, a) ∧ r = none ∧ x = (.idle, none) :=
  driverLTS_mtr_clear_between_poll_and_read_iff a b r₀ r x

end CSLibExtTest.Foundations.Semantics.Peripheral.SampleReadyProtocol
