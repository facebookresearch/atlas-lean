/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.RotatingCoordinator.Run

/-!
# Safety of rotating-coordinator consensus

Chandra and Toueg, *Unreliable failure detectors for reliable distributed systems*, JACM 43(2),
1996, §6.2. Lemma 6.2.1 (pp. 244–245) compares a majority that acknowledged a round with the
reports actually received by a later coordinator. Their common member has not gone backwards in
local time. The chosen maximum timestamp therefore lies at or above the lock. For the selection
of a coordinator that suspects itself before its loopback arrives, the last **value** write can
be newer than the last **timestamp** write. Both writes are earlier than the next report;
the same round induction applies. The safety clauses of Theorem 6.2.3 (p. 246) concern every
process, including one that decides before crashing. In fact agreement and strictly earlier
proposal origin hold already of the *delivered payloads*, regardless of when a receiver arms its
handler. The at-most-once conclusion concerns the first local delivery after invocation, not
per-message duplicate suppression by broadcast. The whole-run safety abstraction permits repeated
polling at an enabled instruction. There is no termination theorem or Byzantine guarantee.
-/

@[expose] public section

namespace Cslib.Distributed.RotatingCoordinator

variable {n : ℕ} {V : Type*} {ev : ℕ → Event n V} {T t : ℕ}

private theorem last_write {A : Type*} {f : Event n V → Option A} {a : A}
    (h : latest ev f t = some a) :
    ∃ i < t, f (ev i) = some a ∧ ∀ j, i < j → j < t → f (ev j) = none := by
  induction t with
  | zero => cases h
  | succ k ih =>
    cases e : f (ev k) with
    | some b => exact ⟨k, by omega, by simpa [latest, e] using h, by omega⟩
    | none =>
      obtain ⟨i, hi, ha, hn⟩ := ih (by simpa [latest, e] using h)
      refine ⟨i, by omega, ha, fun j hj hk => ?_⟩
      rcases Nat.lt_or_ge j k with h | h
      · exact hn j hj h
      · rwa [show j = k by omega]

/-- Estimate timestamps never decrease along the trace of a single process. -/
theorem stamp_mono (ev : ℕ → Event n V) (p : Proc n) : Monotone (stamp ev p) :=
  monotone_nat_of_le_succ fun _ => Nat.le_max_left ..

private theorem stamp_witness {p : Proc n} (h : 0 < stamp ev p t) :
    ∃ i < t, ∃ v, ev i = .ack p (stamp ev p t) v := by
  induction t with
  | zero => cases h
  | succ k ih =>
    by_cases hn : (ev k).adoption p ≤ stamp ev p k
    · rw [stamp, max_eq_left hn] at *
      obtain ⟨i, hi, v, e⟩ := ih h
      exact ⟨i, by omega, v, e⟩
    · have hp : 0 < (ev k).adoption p := by omega
      rw [stamp, max_eq_right (by omega)]
      refine ⟨k, by omega, ?_⟩
      cases e : ev k <;> simp_all [Event.adoption] ; split_ifs at hp <;> simp_all

variable [DecidableEq V] {F : FailureDetector.FailurePattern (Proc n)}
    {H : FailureDetector.History (Proc n)}

private theorem guardAt (h : ProgramPrefix ev F H T) {e : Event n V} (ht : t < T)
    (he : ev t = e) : Guard ev H t e := he ▸ (h ⟨t, ht⟩).2.2

private theorem slots (h : ProgramPrefix ev F H T) {i j : ℕ} (hj : j < T) (hij : i < j)
    (p : Proc n) (hp : (ev j).slot p ≠ 0) : (ev i).slot p < (ev j).slot p :=
  (h ⟨j, hj⟩).2.1 p hp ⟨i, hij⟩

/-- A process invokes `propose` at most once in a program prefix: if `i,j < T` both carry
proposals by `p`, then `i = j`. The process need not be forever correct. -/
theorem ProgramPrefix.propose_time_unique (h : ProgramPrefix ev F H T) {i j : ℕ} {p : Proc n}
    {v w : V} (hi : i < T) (hj : j < T) (ei : ev i = .propose p v) (ej : ev j = .propose p w) :
    i = j := by
  have si : (ev i).slot p = 1 := by simp [ei, Event.slot, Event.actor]
  have sj : (ev j).slot p = 1 := by simp [ej, Event.slot, Event.actor]
  rcases lt_trichotomy i j with lt | eq | gt
  · have := slots h hj lt p (by omega); omega
  · exact eq
  · have := slots h hi gt p (by omega); omega

/-- In a program prefix before `T`, if `t < T` and the event at `t` is `ack p r v`, then the
timestamp `stamp ev p (t + 1)` is exactly `r`. Local order is essential for this equality. -/
theorem stamp_after_ack (h : ProgramPrefix ev F H T) {p : Proc n} {r : ℕ} {v : V}
    (ht : t < T) (he : ev t = .ack p r v) : stamp ev p (t + 1) = r := by
  have bound : stamp ev p t ≤ r := by
    by_contra! hg
    obtain ⟨i, hi, u, ei⟩ := stamp_witness (by omega : 0 < stamp ev p t)
    have hlt := slots h ht hi p (by simp [he, Event.slot, Event.actor])
    simp [he, ei, Event.slot, Event.actor] at hlt
    omega
  simp [stamp, he, Event.adoption, max_eq_right bound]

omit [DecidableEq V] in
private theorem select_at {r : ℕ} {v : V} (h : latest ev (Event.selection r) t = some v) :
    ∃ i < t, ∃ s, ev i = .choose r s v := by
  obtain ⟨i, hi, he, -⟩ := last_write h
  refine ⟨i, hi, ?_⟩
  cases e : ev i <;> simp_all [Event.selection, ite_eq_iff']

private theorem send_before_receive (h : ProgramPrefix ev F H T) {m : Wire n V}
    (ht : t < T) (e : ev t = .receive m) : ∃ i < t, (ev i).sent = some m := by
  obtain ⟨i, hi⟩ := (guardAt h ht e).1
  exact ⟨i, i.isLt, hi⟩

private theorem ack_source (h : ProgramPrefix ev F H T) {p : Proc n} {r : ℕ} {v : V}
    (ht : t < T) (he : ev t = .ack p r v) : ∃ i < t, ∃ s, ev i = .choose r s v := by
  obtain ⟨d, hd, hin, -⟩ := last_write (guardAt h ht he).2
  have hr : ev d = .receive (.suggest p r v) := by
    cases e : ev d with
    | receive m => cases m <;> simp_all [Event.suggested, ite_eq_iff']
    | _ => simp_all [Event.suggested]
  obtain ⟨a, ha, hw⟩ := send_before_receive h (by omega) hr
  have hs : ev a = .send p r v := by cases e : ev a <;> simp_all [Event.sent]
  obtain ⟨i, hi, b, hb⟩ := select_at (guardAt h (by omega) hs).1
  exact ⟨i, by omega, b, hb⟩

private theorem report_sent (h : ProgramPrefix ev F H T) {p : Proc n} {r s : ℕ} {v : V}
    (ht : t < T) (hr : latest ev (Event.incoming r p) t = some (s, v)) :
    ∃ i < t, ev i = .report p r s v := by
  obtain ⟨d, hd, hin, -⟩ := last_write hr
  have hr : ev d = .receive (.report p r s v) := by
    cases e : ev d with
    | receive m => cases m <;> simp_all [Event.incoming, ite_eq_iff']
    | _ => simp_all [Event.incoming]
  obtain ⟨a, ha, hw⟩ := send_before_receive h (by omega) hr
  exact ⟨a, by omega, by cases e : ev a <;> simp_all [Event.sent]⟩

omit [DecidableEq V] in
private theorem write_slots {p : Proc n} {e : Event n V} {b : ℕ} {v : V}
    (hw : e.writeAt p = some (b, v)) : 0 < e.slot p ∧ e.slot p ≤ 5 * b + 4 ∧
      (b = 0 ∨ 5 * b + 3 ≤ e.slot p) := by
  cases e <;> simp_all [Event.writeAt, ite_eq_iff', Event.slot, Event.actor]; omega

-- The last value write need not be the last timestamp write (Phase 2 before a self-NACK).
private theorem report_origin (h : ProgramPrefix ev F H T) {p : Proc n} {k s : ℕ} {v : V}
    (ht : t < T) (hr : ev t = .report p k s v) :
    (s = 0 ∧ ∃ i < t, ev i = .propose p v) ∨
      ∃ b, s ≤ b ∧ b < k ∧ ∃ i < t, ∃ u, ev i = .choose b u v := by
  obtain ⟨hk, -, hv, rfl⟩ := guardAt h ht hr
  obtain ⟨x, hx, hval⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨b, w⟩ := x
  subst v
  obtain ⟨i, hi, hw, hn⟩ := last_write hx
  obtain ⟨hpos, hle, hlo⟩ := write_slots hw
  have hip := slots h ht hi p (by simp [hr, Event.slot, Event.actor])
  rw [show (ev t).slot p = 5 * k + 2 by simp [hr, Event.slot, Event.actor]] at hip
  have hbk : b < k := by omega
  have hsb : stamp ev p t ≤ b := by
    by_contra! hg
    obtain ⟨a, ha, u, he⟩ := stamp_witness (by omega : 0 < stamp ev p t)
    have hai : a ≤ i := by
      by_contra! hia
      have := hn a hia ha
      simp [he, Event.writeAt] at this
    have hl : (ev a).slot p ≤ (ev i).slot p := by
      rcases hai.lt_or_eq with hj | rfl
      · exact (slots h (by omega) hj p (by omega)).le
      · rfl
    rw [show (ev a).slot p = 5 * stamp ev p t + 4 by simp [he, Event.slot, Event.actor]] at hl
    omega
  cases he : ev i with
  | propose q v =>
    simp [he, Event.writeAt, ite_eq_iff'] at hw
    exact .inl ⟨by grind, i, hi, by grind⟩
  | choose r u v =>
    simp only [he, Event.writeAt, ite_eq_iff', Option.some.injEq, Prod.mk.injEq,
      reduceCtorEq] at hw
    exact .inr ⟨b, hsb, hbk, i, hi, u, by grind⟩
  | ack q r v =>
    simp only [he, Event.writeAt, ite_eq_iff', Option.some.injEq, Prod.mk.injEq,
      reduceCtorEq] at hw
    obtain ⟨j, hj, u, hu⟩ := ack_source h (lt_trans hi ht) he
    exact .inr ⟨b, hsb, hbk, j, by omega, u, by grind⟩
  | _ => simp [he, Event.writeAt] at hw

private theorem choose_unique (h : ProgramPrefix ev F H T) {i j r s u : ℕ} {v w : V}
    (hi : i < T) (hj : j < T) (ei : ev i = .choose r s v) (ej : ev j = .choose r u w) :
    v = w := by
  have si : (ev i).slot (coord n r) = 5 * r + 3 := by simp [ei, Event.slot, Event.actor]
  have sj : (ev j).slot (coord n r) = 5 * r + 3 := by simp [ej, Event.slot, Event.actor]
  rcases lt_trichotomy i j with hl | rfl | hl
  · have := slots h hj hl (coord n r) (by omega); omega
  · simp_all
  · have := slots h hi hl (coord n r) (by omega); omega

/-- The stream contains an `ack p r v` strictly before `T` for each `p` in a strict majority.
On a program prefix these occurrences record adoption of the round's suggestion and the sending
of an ACK; their receipt by the coordinator is not required. -/
def Locked (ev : ℕ → Event n V) (T r : ℕ) (v : V) : Prop :=
  ∃ Q, (Paxos.QuorumSystem.majority (Proc n)).IsQuorum Q ∧
    ∀ p ∈ Q, ∃ i < T, ev i = .ack p r v

private theorem locked_choice (h : ProgramPrefix ev F H T) {r : ℕ} {v : V}
    (hl : Locked ev T r v) : ∃ i < T, ∃ s, ev i = .choose r s v := by
  obtain ⟨Q, hQ, hall⟩ := hl
  obtain ⟨p, hp, -⟩ := (Paxos.QuorumSystem.majority _).inter Q Q hQ hQ
  obtain ⟨i, hi, he⟩ := hall p hp
  obtain ⟨j, hj, s, hs⟩ := ack_source h hi he
  exact ⟨j, lt_trans hj hi, s, hs⟩

private theorem stamp_of_ack_report (h : ProgramPrefix ev F H T) {a d r k b : ℕ} {p : Proc n}
    {v x : V} (ha : a < T) (hd : d < T) (e : ev a = .ack p r v) (f : ev d = .report p k b x)
    (hrk : r < k) : r ≤ b := by
  have sa : (ev a).slot p = 5 * r + 4 := by simp [e, Event.slot, Event.actor]
  have sd : (ev d).slot p = 5 * k + 2 := by simp [f, Event.slot, Event.actor]
  have had : a < d := by
    rcases lt_trichotomy a d with lt | rfl | gt
    · exact lt
    · omega
    · have := slots h ha gt p (by omega); omega
  obtain ⟨-, -, -, rfl⟩ := guardAt h hd f
  have hs := stamp_mono ev p (show a + 1 ≤ d by omega)
  simpa [stamp, e, Event.adoption] using
    (Nat.le_max_right (stamp ev p a) ((ev a).adoption p)).trans hs

/-- **Lock preservation** (Lemma 6.2.1). If a majority sent ACKs for `v` in round `r` in a
program prefix, every selection at `k ≥ r` in that prefix chooses `v`. The comparison is between
round numbers, not the real times at which majorities finish collecting messages. -/
theorem locked_preserved (h : ProgramPrefix ev F H T) {r : ℕ} {v : V} (hl : Locked ev T r v)
    {k t s : ℕ} {w : V} (hrk : r ≤ k) (ht : t < T) (hc : ev t = .choose k s w) : w = v := by
  obtain ⟨c, hcT, z, he⟩ := locked_choice h hl
  have hrpos := (guardAt h hcT he).1
  induction k using Nat.strong_induction_on generalizing t s w with
  | _ k ih =>
    rcases hrk.eq_or_lt with rfl | hrk
    · exact choose_unique h ht hcT hc he
    obtain ⟨-, -, hQ, ⟨q, hwin⟩, hmax⟩ := guardAt h ht hc
    obtain ⟨L, hL, hack⟩ := hl
    obtain ⟨p, hpL, hpQ⟩ := (Paxos.QuorumSystem.majority _).inter _ _ hL hQ
    obtain ⟨a, ha, ea⟩ := hack p hpL
    obtain ⟨⟨b, x⟩, hpx⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hpQ).2
    obtain ⟨d, hd, ed⟩ := report_sent h ht hpx
    have hrb := stamp_of_ack_report h ha (hd.trans ht) ea ed hrk
    have hbs := hmax p
    rw [hpx] at hbs
    change b ≤ s at hbs
    obtain ⟨dw, hdw, ew⟩ := report_sent h ht hwin
    rcases report_origin h (hdw.trans ht) ew with ⟨hz, -⟩ | ⟨j, hsj, hjk, i, hi, u, eu⟩
    · omega
    · exact ih j hjk (le_trans hrb (le_trans hbs hsj)) (by omega) eu

private theorem broadcast_lock (h : ProgramPrefix ev F H T) {r : ℕ} {v : V} (ht : t < T)
    (hb : ev t = .finish r (some v)) : Locked ev T r v ∧ ∃ c < t, ∃ s, ev c = .choose r s v := by
  obtain ⟨-, -, check⟩ := guardAt h ht hb
  split at check <;> rename_i hcard
  · obtain ⟨c, hc, s, es⟩ := select_at check.2
    refine ⟨⟨replies ev t r true, ?_, ?_⟩, c, hc, s, es⟩
    · simpa [Paxos.QuorumSystem.majority, Nat.mul_comm] using hcard
    intro p hp
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hp).2
    have er : ev i = .receive (.reply p r true) := by simpa using hi
    obtain ⟨a, ha, ea⟩ := send_before_receive h (lt_trans i.isLt ht) er
    have haT := ha.trans (i.isLt.trans ht)
    have hv : ∃ w, ev a = .ack p r w := by cases e : ev a <;> simp_all [Event.sent]
    obtain ⟨w, hw⟩ := hv
    obtain ⟨k, hk, u, eu⟩ := ack_source h haT hw
    obtain rfl := choose_unique h (hk.trans haT) (hc.trans ht) eu es
    exact ⟨a, haT, hw⟩
  · cases check

private theorem input_of_choice (h : ProgramPrefix ev F H T) {r s : ℕ} {v : V} (ht : t < T)
    (hc : ev t = .choose r s v) : ∃ p i, i < t ∧ ev i = .propose p v := by
  induction t using Nat.strong_induction_on generalizing r s with
  | _ t ih =>
    obtain ⟨-, -, -, ⟨p, hp⟩, -⟩ := guardAt h ht hc
    obtain ⟨d, hd, he⟩ := report_sent h ht hp
    rcases report_origin h (hd.trans ht) he with ⟨-, i, hi, ei⟩ | ⟨b, -, -, j, hj, u, ej⟩
    · exact ⟨p, i, by omega, ei⟩
    · obtain ⟨q, i, hi, ei⟩ := ih j (by omega) (by omega) ej
      exact ⟨q, i, by omega, ei⟩

private theorem delivery_lock (h : LegalPrefix ev F H T) {p : Proc n} {r : ℕ} {v : V}
    (ht : t < T) (er : ev t = .deliver p r v) :
    Locked ev T r v ∧ ∃ c < t, ∃ s, ev c = .choose r s v := by
  obtain ⟨b, eb⟩ := h.2 ⟨t, ht⟩ p r v er
  obtain ⟨hl, c, hc, s, es⟩ := broadcast_lock h.1 (b.isLt.trans ht) eb
  exact ⟨hl, c, hc.trans b.isLt, s, es⟩

/-- Any two R-delivered decision requests before the cut of a legal prefix carry equal values.
Neither recipient must be correct or have invoked `propose`; the requests can belong to
separate rounds and either upcall may be ignored by its local decision handler. -/
theorem LegalPrefix.agree_of_deliver (h : LegalPrefix ev F H T) {i j r k : ℕ} {p q : Proc n}
    {v w : V} (hi : i < T) (hj : j < T) (ei : ev i = .deliver p r v)
    (ej : ev j = .deliver q k w) : v = w := by
  obtain ⟨hr, c, hc, s, es⟩ := delivery_lock h hi ei
  obtain ⟨hk, d, hd, u, eu⟩ := delivery_lock h hj ej
  rcases le_total r k with le | le
  · exact (locked_preserved h.1 hr le (hd.trans hj) eu).symm
  · exact locked_preserved h.1 hk le (hc.trans hi) es

/-- Every R-delivered request in a legal prefix has the value of a strictly earlier proposal by
some process. This does not assume that the recipient decided, or that the proposer is correct. -/
theorem LegalPrefix.proposed_of_deliver (h : LegalPrefix ev F H T) {p : Proc n} {r : ℕ} {v : V}
    (ht : t < T) (er : ev t = .deliver p r v) : ∃ q i, i < t ∧ ev i = .propose q v := by
  obtain ⟨-, c, hc, s, es⟩ := delivery_lock h ht er
  obtain ⟨q, i, hi, he⟩ := input_of_choice h.1 (hc.trans ht) es
  exact ⟨q, i, hi.trans hc, he⟩

omit [DecidableEq V] in
private theorem not_decides_later {i j : ℕ} {p : Proc n} {v w : V} (lt : i < j)
    (ei : Decides ev p i v) (ej : Decides ev p j w) : False := by
  obtain ⟨r, h⟩ := ei.1
  exact ej.2.2 ⟨i, lt⟩ (by simp [h, Event.upcall]) ei.2.1

/-- Uniform safety before a cut: all decision values agree, two decisions at one process have
the same tick, and each value was proposed at a strictly earlier tick. A decision is the first
R-delivery after the recipient's own proposal; an ignored upcall is not a decision. -/
structure UniformSafety (ev : ℕ → Event n V) (T : ℕ) : Prop where
  agreement : ∀ {i j p q v w}, i < T → j < T → Decides ev p i v → Decides ev q j w → v = w
  integrity : ∀ {i j p v w}, i < T → j < T → Decides ev p i v → Decides ev p j w → i = j
  validity : ∀ {t p v}, t < T → Decides ev p t v → ∃ q i, i < t ∧ ev i = .propose q v

/-- **Rotating-coordinator uniform safety on finite prefixes.** Only the program guards, channel
integrity and earlier Phase 4 origin of decision requests are needed; no eventually accurate
detector, eventual delivery, correct-proposer premise or correct majority is required. The
crash-stop pattern itself has at least one forever-correct process. No process must execute an
enabled instruction by the cut. -/
theorem uniformSafety_of_prefix (h : LegalPrefix ev F H T) : UniformSafety ev T where
  agreement hi hj ei ej := by
    obtain ⟨r, er⟩ := ei.1
    obtain ⟨k, ek⟩ := ej.1
    exact h.agree_of_deliver hi hj er ek
  integrity _ _ ei ej := by
    apply le_antisymm <;> apply le_of_not_gt
    · exact fun hl => not_decides_later hl ej ei
    · exact fun hl => not_decides_later hl ei ej
  validity ht hd := by
    obtain ⟨r, er⟩ := hd.1
    exact h.proposed_of_deliver ht er

/-- **Safety of rotating-coordinator consensus** (Chandra and Toueg, Figure 6, Lemma 6.2.1
and the safety clauses of Theorem 6.2.3). Every prefix of an `ArticleRun` has uniform agreement,
at-most-once local decision and proposed-value validity, even for a process that later crashes.
This safety abstraction uses a permitted history of an eventually strong detector (◇S), a correct
majority, correct-process proposals, reliable channels and reliable broadcast. Scheduling counts
polls even at an enabled instruction; it does not guarantee local instruction progress. A process
decides only on its first R-delivery after invocation. Earlier deliveries are not replayed, a
convention for the pre-invocation case left unspecified in Figure 6. There is no termination
conclusion. -/
theorem ArticleRun.uniformSafety {D : FailureDetector.Detector (Proc n)} (a : ArticleRun ev F D H)
    (T : ℕ) : UniformSafety ev T := uniformSafety_of_prefix (a.legalPrefix T)

end Cslib.Distributed.RotatingCoordinator
