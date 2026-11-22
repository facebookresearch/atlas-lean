/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Goldwasser-Sipser: private coins add no power to interactive proofs

Source:
S. Goldwasser and M. Sipser, "Private coins versus public coins in interactive proof systems",
Proceedings of the Eighteenth Annual ACM Symposium on Theory of Computing (STOC 1986),
59-68 (journal version in Advances in Computing Research 5 (1989), 73-90).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GoldwasserSipser

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Goldwasser-Sipser: private coins add no power to interactive proofs

In the shared `IP` definition the prover never sees the verifier's coins (the transcript
contains verifier messages and prover replies only): those are *private* coins. In a
*public-coin* (Arthur-Merlin) protocol with polynomially many rounds, the prover sees the
verifier's coins at every round, but only the coins revealed so far: the total coin tape
is divided into one block of `chunk` fresh coins per round, the verifier's message in a
round depends only on the prefix revealed up to that round, and the prover in that round
sees only that prefix, never future coins. (Handing the prover the whole tape at once
would collapse the game toward one-round AM.) Goldwasser and Sipser showed the two
models coincide: `IP = AM` with polynomially many rounds, i.e. private coins add no power
to interactive proofs. (The one-round class of the shared file, `AM`, is the `k = 1` case;
the theorem needs polynomially many rounds.)
-/

/-- One public-coin interactive-proof game: as in the shared `IPGame`, but the prover
`P` sees the revealed coin prefix (and the transcript) in each round. `chunk` is the
number of fresh coins per round; at the round with `rounds` rounds remaining out of
`totalRounds`, the revealed prefix is the first `(totalRounds - rounds + 1) * chunk`
coins. The verifier's message depends only on that prefix; the final decision may use
the full coin tape. -/
def PubIPGame (cap chunk : ℕ)
    (Vmsg : List Bool × List Bool × List (List Bool) → List Bool)
    (Vdec : List Bool × List Bool × List (List Bool) → Bool)
    (P : List Bool × List (List Bool) → List Bool) (x coins : List Bool) (rounds : ℕ)
    (totalRounds : ℕ) (transcript : List (List Bool)) : Bool :=
  match rounds with
  | 0 => Vdec (x, coins, transcript)
  | rounds + 1 =>
    let revealed := coins.take (((totalRounds - (rounds + 1) + 1) * chunk))
    let m := Vmsg (x, revealed, transcript)
    let reply := P (revealed, transcript ++ [m])
    if m.length ≤ cap ∧ reply.length ≤ cap then
      PubIPGame cap chunk Vmsg Vdec P x coins rounds totalRounds (transcript ++ [m, reply])
    else false

/-- Public-coin interactive proofs with polynomially many rounds: `r` rounds, `chunk`
fresh coins per round (so `r * chunk` coins in total); completeness `≥ 2/3` (some
prover), soundness `≤ 1/3` (every prover). -/
def PubIP : DecisionComplexityClass :=
  {L | ∃ r q chunk : Polynomial ℕ,
    ∃ Vmsg : List Bool × List Bool × List (List Bool) → List Bool,
    ∃ Vdec : List Bool × List Bool × List (List Bool) → Bool,
    IsPolyTime Vmsg ∧ IsPolyTime Vdec ∧
    ∀ x,
      (L x = true →
        ∃ P : List Bool × List (List Bool) → List Bool,
          3 * Set.ncard {coins :
              Fin ((r.eval x.length) * (chunk.eval x.length)) → Bool |
            PubIPGame (q.eval x.length) (chunk.eval x.length) Vmsg Vdec P
              x (List.ofFn coins) (r.eval x.length) (r.eval x.length) [] = true} ≥
            2 * 2 ^ ((r.eval x.length) * (chunk.eval x.length))) ∧
      (L x = false →
        ∀ P : List Bool × List (List Bool) → List Bool,
          3 * Set.ncard {coins :
              Fin ((r.eval x.length) * (chunk.eval x.length)) → Bool |
            PubIPGame (q.eval x.length) (chunk.eval x.length) Vmsg Vdec P
              x (List.ofFn coins) (r.eval x.length) (r.eval x.length) [] = true} ≤
            2 ^ ((r.eval x.length) * (chunk.eval x.length)))}

/-- **Goldwasser-Sipser: private coins add no power to interactive proofs.** Source: S.
Goldwasser and M. Sipser, "Private coins versus public coins in interactive proof systems",
Proceedings of the Eighteenth Annual ACM Symposium on Theory of Computing (STOC 1986),
59-68 (journal version in Advances in Computing Research 5 (1989), 73-90). -/
public theorem_wanted goldwasser_sipser :
    IP = PubIP

end MetaMathlibExt.Complexity.KeyTheorems.GoldwasserSipser
