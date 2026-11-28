# Finiteness of orbits of ω-words under complete reversible automata is undecidable

For some complete reversible automaton it is undecidable whether a given periodic infinite word has a finite orbit, and for complete reversible automata in general it is undecidable whether some infinite word has a finite orbit.

Let $\mathcal T = (Q, \Sigma, \delta)$ range over complete and reversible S-automata (see [automaton semigroups, monoids and groups](automaton-semigroups.md)), and for $\alpha \in \Sigma^\omega$ let $Q^* \circ \alpha$ be its orbit under all products of states.

**Theorem (D'Angeli, Francoeur, Rodaro and Wächter).**

1. There is a complete and reversible S-automaton $\mathcal T = (Q, \Sigma, \delta)$ for which it is undecidable, given $u \in \Sigma^+$, whether the orbit $Q^* \circ u^\omega$ of the periodic word $u^\omega$ is finite (Proposition 4.3).
2. It is undecidable, given a complete and reversible S-automaton $\mathcal T = (Q, \Sigma, \delta)$, whether some $\alpha \in \Sigma^\omega$ has a finite orbit $Q^* \circ \alpha$ (Proposition 4.4).

Whether some $\omega$-word has an infinite orbit is equivalent to infiniteness of the automaton semigroup, and so undecidable by Gillibert's theorem; the source calls item 2 a reciprocal problem to this finiteness problem in the reversible case. The source also shows that an automaton with an $\omega$-word of finite orbit has an ultimately periodic one, though not always a periodic one.

## Depends on

- [Automaton semigroups, monoids and groups](automaton-semigroups.md)

## Proof depends on

- [Some automaton group has undecidable order problem](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group-undecidable-order-problem.md)
- [Positive relations of automaton groups are undecidable](positive-relations-of-automaton-groups-undecidable.md)

## Expansion

Both items pass to the dual automaton $\partial\mathcal T$ of a G-automaton $\mathcal T$, which is complete and reversible, using the source's theorem that a state sequence $\boldsymbol q$ has finite order in $\mathscr G(\mathcal T)$ iff the periodic word $(\overleftarrow{\boldsymbol q})^\omega$ has a finite orbit under $\partial\mathcal T$, where $\overleftarrow{\boldsymbol q}$ is the reversal of $\boldsymbol q$. Item 1 then reduces the order problem of an automaton group with undecidable order problem (Bartholdi and Mitrofanov; Gillibert). Item 2 reduces the existence of a nonempty state sequence acting as the identity (positive relations), using also that a finite orbit implies a periodic word with finite orbit. The torsion–dual-orbit correspondence and the passage from finite orbits to periodic ones have no page.

## Sources

- Daniele D'Angeli, Dominik Francoeur, Emanuele Rodaro and Jan Philipp Wächter, "On the orbits of automaton semigroups and groups", *Algebra and Discrete Mathematics* 33(1), 2022, pp. 1–29, doi:[10.12958/adm1692](https://doi.org/10.12958/adm1692); read in arXiv:2007.10273v1 ([arXiv](https://arxiv.org/abs/2007.10273v1)), whose numbering is used: the abstract and Section 4 (Propositions 4.3 and 4.4 and their proofs).
