/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PathCorrect
public import CSLibExt.Computability.Complexity.PathMachine
public import CSLibExt.Computability.Complexity.Host

/-!
# PATH ∈ P

Sipser, Theorem 7.14, on the canonical classes: the marking machine `Path.Machine` in the decider
host (`Host.isPolyTime_decider`) computes `pathCheck` in polynomial time
(`isPolyTime_pathCheck`), and `pathCheck` decides PATH (`pathDec_eq_pathCheck`), so
`pathDec ∈ P` (`pathDec_mem_P`).
-/

@[expose] public section

namespace Cslib.Complexity.Path

open MetaMathlibExt.ComplexityTheory

instance Machine.instFintypeΓ (k : Machine.K) : Fintype (Machine.Γ k) := by
  cases k <;> infer_instance

/-- **The marking machine as a host component.** The component machine whose stack indices,
stack alphabets, labels and program are those of the marking machine, with its eleven stacks
listed once each, in the order: input, output, edge bits, junk, the counters for the source, the
target and the number of vertices, the counters for the two ends of an arc, the marks and the
parked marks. -/
abbrev pathComp : Host.Comp where
  K := Machine.K
  Γ := Machine.Γ
  L := Machine.Lab
  prog := Machine.prog
  ks := [.X, .O, .E, .J, .S, .T, .N, .U, .V, .M, .P]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The marking algorithm is polynomial-time.** The marking algorithm for PATH, as a function
from bit strings to booleans, is computable in polynomial time by a Turing machine with respect
to the canonical bitstring encodings of lists of booleans and of booleans. -/
theorem isPolyTime_pathCheck : IsPolyTime pathCheck :=
  Host.isPolyTime_decider (c := pathComp) (cX := Machine.K.X) (cO := Machine.K.O)
    (gX := SatVerifier.Sym.bit) (start := Machine.start) (done := Machine.Lab.done)
    (Equiv.refl Bool) pathCheck (Polynomial.C 8 * (Polynomial.X + 1) ^ 4) rfl fun x => by
      obtain ⟨v', S', r, h⟩ := Machine.run x false (Function.update (fun _ => [])
        Machine.K.X (x.map SatVerifier.Sym.bit)) (by simp) (fun k hk => by simp [hk])
      exact ⟨v', S', r.mono (le_of_eq (by simp)), by simpa using h⟩

/-- **PATH ∈ P** (Sipser, Theorem 7.14). The decision problem PATH belongs to the class P of
decision problems decidable in polynomial time. Here PATH accepts a bit string exactly when it
encodes natural numbers $s$, $t$, $n$ and a list $E$ of pairs of natural numbers such that
$s < n$, $t < n$ and $t$ is reachable from $s$ in zero or more steps along the arcs of $E$ below
$n$, the pairs $(u, v) \in E$ with $u < n$ and $v < n$. -/
theorem pathDec_mem_P : pathDec ∈ P := by
  show IsPolyTime pathDec
  rw [show pathDec = pathCheck from funext pathDec_eq_pathCheck]
  exact isPolyTime_pathCheck

end Cslib.Complexity.Path
