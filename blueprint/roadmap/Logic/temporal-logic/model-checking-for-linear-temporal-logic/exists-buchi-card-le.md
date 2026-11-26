# Vardi–Wolper translation with an exponential state bound

For every LTL formula $\varphi$ and every valuation of its atoms on the input letters, some
nondeterministic Büchi automaton with at most $4^{|\varphi|}$ states accepts exactly the
infinite words that satisfy $\varphi$.

Vardi's Corollary 23 states $2^{O(|\varphi|)}$ states for automata over the alphabet $2^{Prop}$;
the statement here gives the explicit constant $4^{|\varphi|} = 2^{2|\varphi|}$ and allows an
arbitrary alphabet whose letters are read through the valuation ($2^{Prop}$ is the case of sets
of atoms read by membership). Vardi derives the corollary from a linear translation into
alternating Büchi automata (his Theorem 22) followed by the exponential removal of alternation
(his Proposition 20); the proof here instead counts the states of a direct truth-annotation
tableau, closer to the direct proof of Vardi and Wolper (1994). Together with the linear-time
emptiness test, this gives the exponential-time procedures for LTL satisfiability and model
checking; the sharper PSPACE bounds are due to Sistla and Clarke.

## Informally uses

- [Exponential state bound for the Büchi automaton of an LTL formula](nat-card-buchi-state-le.md):
  the bound on the automaton used.
- [Büchi automaton language equals the LTL formula language](language-buchi.md): its language.

## Background

- [Every LTL formula has a finite-state Büchi automaton](exists-buchi.md): the same translation
  without a bound on the number of states.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 3, Theorem 22 and Corollary 23.
- M. Y. Vardi and P. Wolper, "Reasoning about infinite computations", *Information and Computation* 115 (1994), 1-37.
