# Topological and ambiguity properties of blind-counter ω-languages are undecidable

Petri nets running over infinite words can be seen as Büchi automata with blind counters, which cannot test for zero. Already for one blind counter it is undecidable whether the accepted ω-language is Borel, regular, or accepted by an unambiguous Petri net, and with four blind counters the arithmetical class of the language is $\Pi^1_2$-complete to determine.

**Setting (Finkel and Skrzypczak).** A *real-time $k$-counter machine* $\mathcal{M} = (K, \Sigma, \Delta, q_0)$ has a finite set $K$ of states, an input alphabet $\Sigma$, an initial state $q_0$ and transitions $(q, a, i_1, \dots, i_k, q', j_1, \dots, j_k) \in \Delta$ with $i_m \in \{0, 1\}$ and $j_m \in \{-1, 0, 1\}$: reading the letter $a$ in state $q$ with counter values $c_m$, where $i_m = 0$ exactly when $c_m = 0$, it moves to $q'$ and adds $j_m$ to each counter, never decrementing a zero counter. The counters are *blind* if every transition enabled with $i_m = 0$ is also enabled with $i_m = 1$, so the machine cannot detect that a counter is zero. A run on an ω-word starts from $(q_0, 0, \dots, 0)$ and reads one letter per step; a *Büchi $k$-blind-counter automaton* adds a set $F \subseteq K$ of accepting states and accepts the ω-words with a run visiting $F$ infinitely often. A Petri net running over ω-words is such an automaton whose counters, one per unbounded place, are partially blind, and the transitions' labels are the input letters. An automaton is *unambiguous* if every ω-word has at most one accepting run. Let $(\mathcal{P}_z)_{z \in \mathbb{N}}$ be an effective enumeration of the real-time Büchi $4$-blind-counter automata over a fixed alphabet. For an ω-language $L \subseteq \Sigma^\omega$, the *arithmetical classes* $\Sigma^0_n$ and $\Pi^0_n$ are the effective (lightface) Borel classes of the Cantor-space topology on $\Sigma^\omega$: $\Sigma^0_1$ consists of the sets $W \cdot \Sigma^\omega$ for recursively enumerable $W \subseteq \Sigma^*$, $\Pi^0_n$ of the complements of $\Sigma^0_n$ sets, and $\Sigma^0_{n+1}$ of the effective countable unions of $\Pi^0_n$ sets; $\boldsymbol{\Sigma}^0_\alpha$ and $\boldsymbol{\Pi}^0_\alpha$ are the boldface Borel classes. These are classes of sets of infinite words, an analogue of the arithmetical classes of sets of natural numbers; the index sets $\{ z : \dots \}$ in clause 1 are sets of natural numbers, and their $\Pi^1_2$-completeness refers to the analytical hierarchy on $\mathbb{N}$.

**Theorem (Finkel and Skrzypczak).**

1. For every $n \ge 2$, the sets $\{ z : L(\mathcal{P}_z) \text{ is in the arithmetical class } \Sigma^0_n \}$, $\{ z : L(\mathcal{P}_z) \text{ is in the arithmetical class } \Pi^0_n \}$ and $\{ z : L(\mathcal{P}_z) \text{ is a } \Delta^1_1 \text{ set} \}$ are $\Pi^1_2$-complete.
2. Given a real-time Büchi $1$-blind-counter automaton $\mathcal{A}$, it is undecidable whether $L(\mathcal{A})$ is Borel, and whether it lies in the Borel class $\boldsymbol{\Sigma}^0_\alpha$ or $\boldsymbol{\Pi}^0_\alpha$ for a given countable ordinal $\alpha$; whether it is an effective $\Delta^1_1$ set, or in the arithmetical class $\Sigma^0_n$ or $\Pi^0_n$ for a given $n \ge 1$; whether it is regular, accepted by a deterministic Petri net, or accepted by a deterministic Turing machine; whether its complement is accepted by a Petri net or by a Turing machine; whether it is accepted by an unambiguous Petri net; and whether it has the maximal degree of ambiguity with respect to acceptance by Petri nets or by Turing machines.

For four blind counters, inclusion and equivalence of the accepted ω-languages are $\Pi^1_2$-complete in the same paper. The exact complexity of the one-counter problems in clause 2 is left open.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [The arithmetical class $\Sigma_n$](../../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Clause 1 transfers the corresponding $\Pi^1_2$-completeness results for real-time Büchi one-counter automata with zero tests through a computable reduction that simulates a one-counter automaton by a $4$-blind-counter automaton up to a computable coding. For clause 2, the paper builds a real-time Büchi $1$-blind-counter automaton $\mathcal{A}_1$ whose ω-language $L_1$ is $\boldsymbol{\Sigma}^1_1$-complete, reducing the ill-founded linear orders on $\mathbb{N}$. For a given $1$-blind-counter automaton with ω-language $L$, the shuffle $S = \mathrm{Sh}(L_1, \Sigma^\omega) \cup \mathrm{Sh}(\Sigma^\omega, L)$ is again accepted by a $1$-blind-counter automaton; it equals $\Sigma^\omega$ when $L = \Sigma^\omega$ and is $\boldsymbol{\Sigma}^1_1$-complete, hence not Borel, otherwise. Each listed property separates these two cases, so universality of $1$-blind-counter Büchi automata, proved undecidable by Böhm, Göller, Halfon and Hofman, reduces to it. A good expansion links pages for that universality result, for the $\Pi^1_2$-completeness of arithmetical classes of one-counter ω-languages, and for the $\boldsymbol{\Sigma}^1_1$-complete $1$-blind-counter ω-language. A good expansion also links a page for the analytical hierarchy ($\Pi^1_2$, $\Delta^1_1$), which clause 1 uses in its statement.

## Sources

- Olivier Finkel and Michał Skrzypczak, *On the Expressive Power of Non-deterministic and Unambiguous Petri Nets over Infinite Words*, Fundamenta Informaticae 183(3–4), 2021, pp. 243–291, https://doi.org/10.3233/FI-2021-2088; the definitions of real-time Büchi counter automata, the theorem on arithmetical classes of $4$-blind-counter ω-languages and the undecidability theorems for $1$-blind-counter automata in the sections on high undecidability and inherent non-determinism, read in arXiv:2107.04025v2.
