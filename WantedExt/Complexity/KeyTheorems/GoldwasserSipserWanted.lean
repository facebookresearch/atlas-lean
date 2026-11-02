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

/-- **Public-coin interactive-proof game.** The game takes a length cap $c$, a number $k$ of
fresh coins per round, a verifier message function $V_{\mathrm{msg}}$, a verifier decision
function $V_{\mathrm{dec}}$, a prover $P$ mapping pairs of a coin prefix and a transcript (a list
of bitstrings) to bitstrings, an input $x$, a coin string $\rho$, a number $j$ of remaining
rounds, a total number $T$ of rounds and a transcript $t$, and returns a Boolean outcome. If
$j = 0$, the outcome is $V_{\mathrm{dec}}(x, \rho, t)$. Otherwise let $\pi$ be the first
$(T - j + 1) k$ coins of $\rho$ (all of $\rho$ if it is shorter), where $T - j$ is truncated
subtraction ($0$ when $j > T$). The verifier sends $m = V_{\mathrm{msg}}(x, \pi, t)$ and the
prover replies $a = P(\pi, t')$, where $t'$ is $t$ extended by $m$. If both $m$ and $a$ have
length at most $c$, the outcome is that of the game with $j - 1$ remaining rounds, the same
$T$, and transcript $t$ extended by $m$ and then $a$; otherwise the outcome is false.

So the verifier's message and the prover's reply in a round see only the coins revealed up to
that round, while the final decision may use the whole coin string. -/
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

/-- **Public-coin interactive proofs.** A decision problem $L$ is in $\mathsf{PubIP}$ when there
are polynomials $r$, $q$ and $k$ with natural-number coefficients and polynomial-time functions
$V_{\mathrm{msg}}$ (the verifier's message function) and $V_{\mathrm{dec}}$ (its decision
function) with the following property. For a bitstring $x$, a prover $P$ (an arbitrary function
from pairs of a coin prefix and a transcript to bitstrings) and a coin string $c$, let $G(P, c)$
be the outcome of the public-coin interactive-proof game with message length cap $q(|x|)$,
$k(|x|)$ fresh coins per round, verifier $V_{\mathrm{msg}}$ and $V_{\mathrm{dec}}$, prover $P$,
input $x$, coins $c$, $r(|x|)$ remaining rounds out of $r(|x|)$ total rounds and the empty
initial transcript. Then for every bitstring $x$: if $L(x)$ is true, some prover $P$ makes
$G(P, c)$ true for at least $2/3$ of the coin strings $c \in \{0,1\}^{r(|x|) k(|x|)}$; and if
$L(x)$ is false, every prover $P$ makes $G(P, c)$ true for at most $1/3$ of them. -/
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

/-- **Goldwasser-Sipser: private coins add no power to interactive proofs.** The class
$\mathsf{IP}$ of decision problems with (private-coin) interactive proofs equals the class
$\mathsf{PubIP}$ of decision problems with public-coin interactive proofs with polynomially many
rounds.

Source: S.
Goldwasser and M. Sipser, "Private coins versus public coins in interactive proof systems",
Proceedings of the Eighteenth Annual ACM Symposium on Theory of Computing (STOC 1986),
59-68 (journal version in Advances in Computing Research 5 (1989), 73-90). -/
public theorem_wanted goldwasser_sipser :
    IP = PubIP

end MetaMathlibExt.Complexity.KeyTheorems.GoldwasserSipser
