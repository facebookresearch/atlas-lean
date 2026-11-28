# Termination of round-delayed amnesiac flooding is undecidable

In round-delayed amnesiac flooding, nodes forward a message to their neighbors without remembering it, while an adversary may block individual transmissions for finitely many rounds at a time. Whether flooding terminates under an arbitrary computable adversary is undecidable; the reduction uses a fixed triangle.

**Setting (Alafin, Mertzios and Spirakis).** The network is a simple, finite, connected graph $G = (V, E)$ with a source node $g_0$ holding a message. An adversary is a *delay function* $d : \mathbb{N} \times V \times E \to \{0, 1\}$, where $d(j, v, e) = 1$ blocks transmission from $v$ along the incident edge $e$ in round $j$; it must have the *finite delay property* (every maximal run of consecutive blocked rounds for a node and edge is finite). Under the round-delayed amnesiac flooding protocol, a node that newly receives the message in a round sets its pending destinations to all neighbors except those that just delivered it; in each round it transmits along the unblocked edges to pending destinations and keeps the blocked ones pending; it holds the message while it receives it or still has pending transmissions, and it keeps no other memory. Flooding *terminates* if from some round on no node holds the message. The problem RDAF-TERMINATION asks, given $G$, $g_0$ and a computable delay function $d$, whether flooding terminates. As an input to an algorithm, $d$ is given by a program that computes it, promised to compute a total function with the finite delay property.

**Theorem (Alafin, Mertzios and Spirakis).** RDAF-TERMINATION is undecidable.

The reduction uses the triangle graph and adversaries that, in round $j$, either block nothing (once a given Turing machine has halted within $j$ steps) or follow a fixed period-$3$ blocking pattern. It still works when the adversary in round $n$ simulates only $\lfloor f(n) \rfloor$ steps of the machine, for any computable $f$ with $f(n) \to \infty$, so that each round costs time and space $O(f(n))$ (Theorem 6 of the source). The same paper shows that termination is decidable for eventually periodic adversaries.

## Depends on

- [Finite simple graph](../../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

On the triangle with nodes $\mathrm{Source}, A, B$, a fixed periodic delay function $d_0$ blocks, in rounds $j \equiv 0, 1, 2 \pmod 3$, every edge except $\{\mathrm{Source}, B\}$, $\{\mathrm{Source}, A\}$ and $\{A, B\}$ respectively, and makes the message circulate forever. For a Turing machine $M$ and input $x$, the computable delay function $d(j, u, e)$ is $0$ if $M$ halts on $x$ within $j$ steps and $d_0(j, u, e)$ otherwise. If $M$ halts after $t$ steps, no transmission is blocked from round $t$ on and flooding terminates by round $t + 2$; if $M$ never halts, $d = d_0$ and flooding never terminates.

## Sources

- Oluwatobi Alafin, George B. Mertzios and Paul G. Spirakis, "Round-delayed amnesiac flooding", Theoretical Computer Science 1075, Article 115956, 2026, <https://doi.org/10.1016/j.tcs.2026.115956>; Section 3 (model, protocol and termination, Definitions 1 and 2), Lemma 6, Theorem 5 (undecidability) and Theorem 6 (resilient undecidability) of Section 6 ("Undecidability with Arbitrary Computable Adversaries"), and Theorem 7 of Section 7 on eventually periodic adversaries, of arXiv:2604.04260v1, read at <https://arxiv.org/abs/2604.04260v1>.
