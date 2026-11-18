/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.ProducerInterruptSimulation

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol
open Cslib.Semantics.Peripheral.PollDriverSimulation
open Cslib.Semantics.Peripheral.ProducerInterruptSimulation

namespace CSLibExtTest.Foundations.Semantics.Peripheral.ProducerInterruptSimulation

/-- The three-poll run of the polling driver, with samples `7` (ID 0) and `9` (ID 1), is a
system trace of the counting producer in which the interrupt never fires; its state is
untouched and observing the wrapped labels gives back the driver labels. -/
example :
    (systemLTS (counterHandler (α := ℕ) id)).MTr (initialSystem (0, false))
        ((threePollRun 7 9).map SystemLabel.driver)
        ⟨(0, false), ⟨.poll, true, some (1, 9), some (1, 9)⟩, none⟩ ∧
      ((threePollRun 7 9).map SystemLabel.driver).map observe = threePollRun 7 9 :=
  systemLTS_mtr_of_pollDriverLTS_mtr _ _ _ _ _ _ _ (threePollRun_valid 7 9).1

/-- The lifted three-poll run erases to the same protocol events as the driver run, and it
delivers only the sample with ID `1`. -/
example :
    systemVisibleLabels ((threePollRun 7 9).map SystemLabel.driver) =
        visibleLabels (threePollRun 7 9) ∧
      deliveredIds (systemVisibleLabels ((threePollRun 7 9).map SystemLabel.driver)) = [1] :=
  ⟨rfl, rfl⟩

/-- The emit at index 13 of the lifted three-poll run is fed by a driver read of `some (1, 9)`
preceded by a publication of `(1, 9)` with no publication in between. -/
example :
    ∃ j k, k < j ∧ j < 13 ∧
      ((threePollRun 7 9).map SystemLabel.driver)[j]? =
        some (.driver (.visible (.read (some (1, 9))))) ∧
      (((threePollRun 7 9).map SystemLabel.driver)[k]?).bind publication? = some (1, 9) ∧
      ∀ l : ℕ, k < l → l < j →
        (((threePollRun 7 9).map SystemLabel.driver)[l]?).bind publication? = none :=
  exists_publication_of_deliver (counterHandler (α := ℕ) id) (rely_counterHandler id) (0, false)
    _ _ (systemLTS_mtr_of_pollDriverLTS_mtr _ (0, false) _ _ _ _ _
      (threePollRun_valid 7 9).1).1 13 1 9 rfl

/-- The preemption run over `ℕ` with `sample = (· + 10)`: interrupt publications before the
Ready poll, between the poll and the read, and before the emit. It is a system trace whose
erasure is a protocol trace, and its register operations are the expected four. -/
example :
    (systemLTS (counterHandler (· + 10))).MTr (initialSystem (0, false))
        (preemptionRun (· + 10))
        ⟨(3, false), ⟨.poll, true, some (1, 11), some (1, 11)⟩, some (2, 12)⟩ ∧
      (driverLTS ℕ).MTr (.idle, none) (systemVisibleLabels (preemptionRun (· + 10)))
        (.idle, some (2, 12)) ∧
      registerTrace (preemptionRun (· + 10)) =
        [.publish 0 10, .publish 1 11, .read (some (1, 11)), .publish 2 12] :=
  ⟨(preemptionRun_valid _).1, (preemptionRun_valid _).2.1, (preemptionRun_valid _).2.2.1⟩

/-- The driver delivers the sample with ID `1` that it read, not the newer interrupt
publication with ID `2`. -/
example : deliveredIds (systemVisibleLabels (preemptionRun (· + 10))) = [1] :=
  (preemptionRun_valid _).2.2.2

/-- The emit at index 10 of the preemption run is fed by the driver read at index 6 of the
interrupt's publication at index 5, with no publication in between. -/
example :
    ∃ j k, k < j ∧ j < 10 ∧
      (preemptionRun (· + 10))[j]? = some (.driver (.visible (.read (some (1, 11))))) ∧
      ((preemptionRun (· + 10))[k]?).bind publication? = some (1, 11) ∧
      ∀ l : ℕ, k < l → l < j → ((preemptionRun (· + 10))[l]?).bind publication? = none :=
  (producerInterrupt_correct _ (rely_counterHandler _) _).2.2 _ _ (preemptionRun_valid _).1
    |>.2.2.2.2.2 10 1 11 rfl

/-- On the register trace of the preemption run, the read at index 2 is preceded by its
publication with no publication in between, and read IDs are strictly increasing. -/
example :
    (∃ j, j < 2 ∧ (registerTrace (preemptionRun (· + 10)))[j]? = some (.publish 1 11) ∧
        ∀ k m w, j < k → k < 2 →
          (registerTrace (preemptionRun (· + 10)))[k]? ≠ some (.publish m w)) ∧
      (readIds (registerTrace (preemptionRun (· + 10)))).Pairwise (· < ·) := by
  have h := (producerInterrupt_correct _ (rely_counterHandler (· + 10)) (0, false)).2.2 _ _
    (preemptionRun_valid _).1
  refine ⟨h.2.2.1 2 1 11 rfl, h.2.2.2.2.1 ?_⟩
  rw [(preemptionRun_valid _).2.2.1]
  decide

/-- The counting producer over `ℕ` is similar to the protocol from the initial states. -/
example :
    Cslib.LTS.Similarity (observedLTS (counterHandler (α := ℕ) id)) (protocolLTS ℕ).saturate
      (initialSystem (0, false)) (.idle, none) := by
  unfold Cslib.LTS.Similarity
  exact ⟨systemRefinement, systemRefinement_initial _,
    isSimulation_systemRefinement _ (rely_counterHandler id)⟩

/-- Overwriting the driver's cache with `(5, 7)` or its loaded data with `(1, 9)` violates the
rely condition. -/
example :
    ¬ Rely (cacheClobberHandler ((5, 7) : ℕ × ℕ)) ∧
      ¬ Rely (dataClobberHandler ((1, 9) : ℕ × ℕ)) :=
  ⟨not_rely_cacheClobberHandler _, not_rely_dataClobberHandler _⟩

/-- The rely condition is sufficient, not necessary: the cache-clobbering handler violates it,
yet the refinement relation is still a simulation, because the protocol never observes the
cache. -/
example :
    Cslib.LTS.IsSimulation (observedLTS (cacheClobberHandler ((5, 7) : ℕ × ℕ)))
      (protocolLTS ℕ).saturate systemRefinement := by
  rintro x y hr l x' ⟨m, rfl, htr⟩
  change y = _ at hr
  subst hr
  change SystemStep _ x m x' at htr
  cases htr with
  | driver q h => exact isSimulation_refinement rfl _ _ h
  | interrupt h =>
      cases h with
      | clobber => exact ⟨_, Cslib.LTS.STr.refl, rfl⟩

/-- With samples `7` and `9`, the data-clobbering run is a system trace whose erasure is no
protocol trace and whose emitted sample `(1, 9)` was never published. -/
example :
    (∃ x, (systemLTS (dataClobberHandler (1, 9))).MTr (initialSystem ()) (dataClobberRun 7 9)
        x) ∧
      (¬ ∃ y, (driverLTS ℕ).MTr (.idle, none) (systemVisibleLabels (dataClobberRun 7 9)) y) ∧
      ∀ k : ℕ, ((dataClobberRun 7 9)[k]?).bind publication? ≠ some (1, 9) :=
  dataClobberRun_not_protocol_trace 7 9

/-- The data-clobbering system over `ℕ` is not similar to the protocol from the initial
states. -/
example :
    ¬ Cslib.LTS.Similarity (observedLTS (dataClobberHandler ((1, 9) : ℕ × ℕ)))
      (protocolLTS ℕ).saturate (initialSystem ()) (.idle, none) :=
  not_similarity_dataClobber 7 9

end CSLibExtTest.Foundations.Semantics.Peripheral.ProducerInterruptSimulation
