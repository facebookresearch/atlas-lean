# Bounded model checking for existential LTL

Let $M$ be a finite Kripke structure with initial states, in which every state has a successor and states are encoded by Boolean vectors, and let $f$ be an LTL formula. Then $M \models \mathbf{E} f$ (some path from an initial state satisfies $f$) if and only if $M \models_k \mathbf{E} f$ for some $k$, where $\models_k$ is the bounded semantics on paths $s_0, \dots, s_k$ from an initial state, read as a $(k, l)$-loop when $s_k \to s_l$ for some $l \le k$ and otherwise as a prefix with no final back-loop, in which earlier states may repeat but $s_k$ has no transition to any $s_l$ with $l \le k$; and for every $k$ the propositional formula $[\![M, f]\!]_k$, the conjunction of the initial-state predicate and $k$ copies of the transition relation with the disjunction of the no-back-loop condition together with the bounded translation of $f$ and, for each $l \le k$, the loop condition for $(k, l)$ together with the translation of $f$ for that loop, is satisfiable if and only if $M \models_k \mathbf{E} f$.

## Depends on

- [Satisfaction of LTL formulas on ω-words](../../../Logic/temporal-logic/linear-temporal-logic/satisfies.md)
- [Satisfiability of a CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)
- [Kripke structures with initial states](../../../Logic/temporal-logic/temporal-specification/kripke-structures-with-initial-states.md)

## Sources

- A. Biere, A. Cimatti, E. Clarke and Y. Zhu, "Symbolic model checking without BDDs", *TACAS 1999*, LNCS 1579, Springer, 1999, Definitions 1 and 4–15, Theorem 9, Theorem 16 and Corollary 17, <https://fmv.jku.at/papers/BiereCimattiClarkeZhu-TACAS99.pdf>
