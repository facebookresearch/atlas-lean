/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.BinarySearch
public meta import CSLibExt.Languages.MiniImp.BinarySearch

open CSLibExt.Languages.MiniImp
open CSLibExt.Languages.MiniImp.BinarySearch

private def observe (fuel : Nat) (c : Stmt) (s : State) (x : String) :
    Option Nat × Nat :=
  let r := execReads fuel c s
  (r.ret.map (fun t => t x), r.time)

-- Independently fixed counts: always left vs always right at each midpoint.
private def fixtures : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (1, 1, 1), (2, 2, 1), (3, 2, 2),
    (7, 3, 3), (8, 4, 3), (15, 4, 4), (16, 5, 4)]

private def edgeChecks : Bool := fixtures.all fun (n, left, right) =>
  let xs := Array.replicate n 4
  let runAt := fun key => observe (n + 7) (program xs key) (fun _ => 37) "lo"
  runAt 3 == (some 0, left) && runAt 4 == (some 0, left) &&
    runAt 5 == (some n, right)

-- Named private checks keep their proof closures available to the audit.
private theorem edges_checked : edgeChecks = true := by decide
private theorem duplicate_present :
    observe 11 (program #[1, 3, 3, 7] 3) (fun _ => 99) "lo" =
      (some 1, 3) := by decide
private theorem duplicate_absent :
    observe 11 (program #[1, 3, 3, 7] 4) (fun _ => 99) "lo" =
      (some 3, 2) := by decide

#eval do
  unless edgeChecks do throw (IO.userError "independent count mismatch")
  IO.println "PASS 24 independent size/key read-count and index fixtures"
  for (n, _, _) in fixtures do
    let xs := Array.replicate n 4
    IO.println (n, observe (n + 7) (program xs 4) (fun _ => 37) "lo",
      observe (n + 7) (program xs 5) (fun _ => 37) "lo")

private def goodRead : Stmt := .read "x" #[7] (.lit 0)
private def badRead : Stmt := .read "x" #[7] (.lit 1)

private def prefixChecks : Bool :=
  let run := fun f c => observe f c (fun _ => 99) "x"
  run 0 goodRead == (none, 0) && run 1 badRead == (none, 0) &&
    run 2 (.seq goodRead badRead) == (none, 1) &&
    run 2 (.seq badRead goodRead) == (none, 0) &&
    run 2 (.seq goodRead (.seq .skip .skip)) == (none, 1) &&
    run 3 (.if_ .tru (.seq goodRead goodRead) badRead) == (some 7, 2) &&
    run 3 (.if_ (.not .tru) badRead goodRead) == (some 7, 1) &&
    run 3 (.while .tru (fun _ => False) goodRead) == (none, 2)

private theorem prefixes_checked : prefixChecks = true := by decide

-- A real linear scan, not an arbitrary tick annotation: eight checked reads.
private def linearScan : Stmt :=
  .seq (.assign "i" (.lit 0))
    (.while (.not (.le (.lit 8) (.var "i"))) (fun _ => True)
      (.seq (.read "x" #[0, 1, 2, 3, 4, 5, 6, 7] (.var "i"))
        (.assign "i" (.add (.var "i") (.lit 1)))))

private theorem scan_result :
    observe 20 linearScan (fun _ => 99) "i" = (some 8, 8) := by decide
private theorem scan_exceeds_binary_bound :
    Nat.clog 2 (8 + 1) < (execReads 20 linearScan (fun _ => 99)).time := by
  decide
private theorem wrong_count_refuted :
    (execReads 1 goodRead (fun _ => 99)).time ≠ 0 := by decide

#eval do
  unless prefixChecks do throw (IO.userError "prefix/failure mismatch")
  let scan := observe 20 linearScan (fun _ => 99) "i"
  unless scan == (some 8, 8) && Nat.clog 2 9 < scan.2 do
    throw (IO.userError "linear scan failed to falsify the binary bound")
  IO.println s!"PASS 8 prefix/failure cases; linear scan {scan}, bound=4"

-- Replay the composed theorem on a populated, duplicate-key input.
private theorem composed_client (s : State) : ∃ t,
    ReadSteps (program #[1, 3, 3, 7] 3) s t 3 ∧
    BigStep (program #[1, 3, 3, 7] 3) s t ∧ t "lo" = 1 := by
  obtain ⟨t, _, he, hc, htime, _, _, hhoare, _⟩ :=
    verified_read_cost #[1, 3, 3, 7] 3 s (by decide)
  have hn : (execReads (#[1, 3, 3, 7].size + 7)
      (program #[1, 3, 3, 7] 3) s).time = 3 :=
    htime.trans (by decide +kernel)
  rw [hn] at hc
  exact ⟨t, hc, hc.erase,
    (hhoare s t trivial (exec_sound he)).trans (by decide +kernel)⟩

private theorem assignment_counted (s : State) :
    ∃ n, ReadSteps (.assign "x" (.lit 7)) s (s.update "x" 7) n :=
  BigStep.exists_readSteps .assign
private theorem invalid_not_counted (s t : State) (n : Nat) :
    ¬ ReadSteps badRead s t n := by
  intro h
  exact read_no_bigStep (by simp [evalA]) h.erase
private theorem invalid_cost_zero (fuel : Nat) (s : State) :
    execReads fuel badRead s = pure none :=
  execReads_read_invalid fuel (by simp [evalA])
private theorem failed_prefix_retained {fuel : Nat} {s : State}
    (h : (execReads fuel (.seq goodRead badRead) s).ret = none) :
    execReads (fuel + 1) (.seq (.seq goodRead badRead) goodRead) s =
      execReads fuel (.seq goodRead badRead) s := execReads_seq_failed h

private def arraysOfLength : Nat → List (Array Nat)
  | 0 => [#[]]
  | n + 1 => (arraysOfLength n).flatMap (fun xs => (List.range 4).map xs.push)

#eval do
  let mut full := 0
  for xs in (List.range 6).flatMap arraysOfLength do
    for key in List.range 6 do
      let ref := Cslib.Algorithms.Lean.TimeM.lowerBound xs key
      for extra in [0, 6] do
        let got := observe (xs.size + 7 + extra) (program xs key)
          (fun _ => 99) "lo"
        unless got == (some ref.ret, ref.time) do
          throw (IO.userError s!"full cost mismatch: {xs}, {key}, {extra}")
        full := full + 1
  let mut intervals := 0
  for xs in (List.range 4).flatMap arraysOfLength do
    let xs : Array Nat := xs
    for key in List.range 6 do
      for lo in List.range (xs.size + 1) do
        for hi in List.range (xs.size + 1) do
          if h : lo ≤ hi ∧ hi ≤ xs.size then
            let s := State.update (State.update (fun _ => 99) "lo" lo) "hi" hi
            let ref := Cslib.Algorithms.Lean.TimeM.lowerBound.loop
              xs key lo hi h.1 h.2
            let got := observe (hi - lo + 5) (loop xs key) s "lo"
            unless got == (some ref.ret, ref.time) do
              throw (IO.userError s!"interval cost mismatch: {xs}, {key}")
            intervals := intervals + 1
  unless full == 16380 && intervals == 4494 do
    throw (IO.userError s!"wrong count coverage: {full}, {intervals}")
  IO.println s!"PASS {full} full and {intervals} interval cost/index checks"

#print axioms execReads
#print axioms execReads_ret
#print axioms execReads_sound
#print axioms ReadSteps.erase
#print axioms BigStep.exists_readSteps
#print axioms execReads_read_invalid
#print axioms execReads_seq_failed
#print axioms loop_reads_eq_time
#print axioms program_reads_eq_time
#print axioms program_reads_le
#print axioms verified_read_cost
