# Bounded Petri net synthesis from modal transition systems is undecidable

Given a deterministic modal transition system, which specifies required (must) and allowed (may) behavior, it is undecidable whether some bounded Petri net has a reachability language that implements it. The same holds for synthesis of bounded Petri nets satisfying a formula of the conjunctive nu-calculus.

**Setting (Schlachter).** A Petri net $N = (P, \Sigma, F, M_0)$ has finite disjoint sets of places $P$ and transitions $\Sigma$ (each transition is its own label), arc weights $F : (P \times \Sigma) \cup (\Sigma \times P) \to \mathbb{N}$ and an initial marking $M_0 : P \to \mathbb{N}$; a transition fires when every input place holds at least as many tokens as its arc weight. $N$ is *bounded* if some $k$ bounds the number of tokens on every place in every reachable marking, and its language $L(N)$ is the set of firing sequences from $M_0$. A *modal transition system* $\mathcal{M} = (S, \Sigma, \to_\square, \to_\Diamond, s_0)$ has finitely many states, must arcs $\to_\square$ and may arcs $\to_\Diamond$ with $\to_\square \subseteq \to_\Diamond$; it is *deterministic* if its may-arc transition system is. A labeled transition system *implements* $\mathcal{M}$ if some relation containing the pair of initial states makes every must arc of $\mathcal{M}$ matched by a transition of the system and every transition of the system matched by a may arc of $\mathcal{M}$, between related states. A prefix-closed language $L$ implements $\mathcal{M}$, written $L \models \mathcal{M}$, if some deterministic transition system with language $L$ implements it. The *conjunctive nu-calculus* has formulas built from $\mathit{true}$, variables, $\to_a$ ("$a$ is enabled"), $\not\to_a$ ("$a$ is disabled"), $[a]\beta$, $\beta_1 \wedge \beta_2$ and greatest fixed points $\nu X.\beta$, evaluated on prefix-closed languages; a Petri net satisfies a closed formula if its language does at the empty word.

**Theorem (Schlachter).**

1. It is undecidable whether there exists a bounded Petri net, over a fixed set of six transitions, satisfying a given closed formula of the conjunctive nu-calculus.
2. Given a deterministic modal transition system $\mathcal{M}$, it is undecidable whether there exists a bounded Petri net $N$ with $L(N) \models \mathcal{M}$.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Boundedness and safeness of Petri nets](../../../boundedness-and-safeness.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces from the bounded execution problem for two-counter machines: whether the counter values along the machine's unique execution stay bounded, which is undecidable since it would decide halting. A family of bounded nets $N_{\mathrm{sim}}(b_0, b_1)$ with six transitions simulates counters bounded by $b_0, b_1$, and a formula $\Phi_C$ describes the execution of the machine $C$ on their reachability graphs, so that some $N_{\mathrm{sim}}(b_0, b_1)$ satisfies $\Phi_C$ exactly when the execution is bounded. A further formula forces every bounded net satisfying it to have the reachability graph of some $N_{\mathrm{sim}}(b_0, b_1)$, which gives part 1. Part 2 follows because closed conjunctive nu-calculus formulas, modal specifications and deterministic modal transition systems are equally expressive.

## Sources

- Uli Schlachter, "Bounded Petri Net Synthesis from Modal Transition Systems is Undecidable", 27th International Conference on Concurrency Theory (CONCUR 2016), LIPIcs 59, Article 15, 2016, <https://doi.org/10.4230/LIPIcs.CONCUR.2016.15>; Definitions 1–3, 5 and 26, Corollary 11, Theorem 25 and Theorem 30 (main statement), read in the open-access copy at <https://drops.dagstuhl.de/storage/00lipics/lipics-vol059-concur2016/LIPIcs.CONCUR.2016.15/LIPIcs.CONCUR.2016.15.pdf>.
