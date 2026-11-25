/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.PollDriverSimulation

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol
open Cslib.Semantics.Peripheral.PollDriverSimulation

namespace CSLibExtTest.Foundations.Semantics.Peripheral.PollDriverSimulation

/-- Three poll iterations with samples `7` (ID 0) and `9` (ID 1): Ready false, then an empty
read after another reader clears the slot, then a successful read. The run is a driver trace
ending with `(1, 9)` loaded and cached and the slot empty. -/
example :
    (pollDriverLTS ℕ).MTr (initialDriver, none) (threePollRun 7 9)
      (⟨.poll, true, some (1, 9), some (1, 9)⟩, none) :=
  (threePollRun_valid 7 9).1

/-- Erasing the internal steps of the three-poll run leaves exactly the protocol events. -/
example :
    visibleLabels (threePollRun 7 9) =
      [.poll false, .retry, .env (.publish 0 7), .poll true, .env (.read (some (0, 7))),
        .read none, .retry, .env (.publish 1 9), .poll true, .read (some (1, 9)),
        .deliver 1 9] :=
  rfl

/-- The erased three-poll run is a protocol trace that delivers only the sample with ID `1`. -/
example :
    (driverLTS ℕ).MTr (.idle, none) (visibleLabels (threePollRun 7 9)) (.idle, none) ∧
      deliveredIds (visibleLabels (threePollRun 7 9)) = [1] :=
  (threePollRun_valid 7 9).2

/-- The three-poll run's register operations form a register trace from the empty slot. -/
example :
    (registerLTS ℕ).MTr none
      ((visibleLabels (threePollRun 7 9)).filterMap registerLabel?) none :=
  (pollDriver_correct.2.2 _ _ (threePollRun_valid 7 9).1).2.1

/-- The emit at index 13 of the three-poll run is fed by a driver read of `some (1, 9)` that
follows the publication `publish 1 9` with no other publication in between. -/
example :
    ∃ j k, k < j ∧ j < 13 ∧
      (threePollRun 7 9)[j]? = some (.visible (.read (some (1, 9)))) ∧
      (threePollRun 7 9)[k]? = some (.visible (.env (.publish 1 9))) ∧
      ∀ l m w, k < l → l < j →
        (threePollRun 7 9)[l]? ≠ some (.visible (.env (.publish m w))) :=
  exists_publish_of_emit _ _ (threePollRun_valid 7 9).1 13 1 9 rfl

/-- The stale-cache run with sample `7` is a trace of the faulty driver whose erasure is no
protocol trace. -/
example :
    (∃ x, (staleCacheDriverLTS ℕ).MTr (initialDriver, none) (staleCacheRun 7) x) ∧
      ¬ ∃ y, (driverLTS ℕ).MTr (.idle, none) (visibleLabels (staleCacheRun 7)) y :=
  staleCacheRun_not_protocol_trace 7

/-- The stale-cache driver over `ℕ` is not similar to the protocol from the initial states,
while the polling driver is. -/
example :
    ¬ Cslib.LTS.Similarity (staleCacheDriverLTS ℕ) (protocolLTS ℕ).saturate
        ((initialDriver, none) : DriverState ℕ × Slot ℕ) (.idle, none) ∧
      Cslib.LTS.Similarity (pollDriverLTS ℕ) (protocolLTS ℕ).saturate
        ((initialDriver, none) : DriverState ℕ × Slot ℕ) (.idle, none) :=
  ⟨not_similarity_staleCacheDriver 7, similarity_initial⟩

end CSLibExtTest.Foundations.Semantics.Peripheral.PollDriverSimulation
