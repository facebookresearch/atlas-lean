# Finiteness of orbits of finite words under an automaton group is undecidable

There is an automaton group for which no algorithm decides whether the orbit of a given finite word is finite; this generalized finiteness problem for automaton groups is equivalent to finiteness of left principal ideals in semigroups of complete reversible automata.

Let $\mathcal T = (Q, \Sigma, \delta)$ range over G-automata (complete, deterministic and inverse-deterministic synchronous automata), generating automaton groups $\mathscr G(\mathcal T)$, and complete reversible S-automata, generating automaton semigroups $\mathscr S(\mathcal T)$ (see [automaton semigroups, monoids and groups](automaton-semigroups.md)). For a word $w$, finite or infinite, its *orbit* $Q^* \circ w$ is the set of its images under all products of states.

**Theorem (D'Angeli, Francoeur, Rodaro and Wächter).**

1. There is a G-automaton $\mathcal T = (Q, \Sigma, \delta)$ such that it is undecidable, given $w \in \Sigma^*$, whether the orbit $\mathscr G(\mathcal T) \cdot w$ is finite (Theorem 3.1).
2. For such a $\mathcal T$, it is undecidable, given $w \in \Sigma^*$, whether some $\omega$-word $\alpha \in \Sigma^\omega$ makes the orbit $Q^* \circ w\alpha$ infinite (Corollary 3.2).
3. It is undecidable, given a complete reversible S-automaton $\mathcal R = (P, \Gamma, \tau)$ and $\boldsymbol p \in P^*$, whether the left principal ideal $P^* \boldsymbol p$ of $\mathscr S(\mathcal R)$ is finite (Corollary 3.3).

The source presents item 1 as a more general version of the finiteness problem for automaton groups (given a G-automaton $\mathcal T$, is $\mathscr G(\mathcal T)$ finite?), whose decidability is an open question; the finiteness problem for automaton semigroups is undecidable (Gillibert).

## Depends on

- [Automaton semigroups, monoids and groups](automaton-semigroups.md)

## Proof depends on

- [Some automaton group has undecidable order problem](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group-undecidable-order-problem.md)

## Expansion

Item 1 uses Gillibert's construction of an automaton group with undecidable order problem: his proof actually shows that it is undecidable whether an element of the special form $\diamond\Lambda(\boldsymbol p)$ has finite order, for a fixed state $\diamond$ (written as a dollar sign in the source), with $\Lambda(\varepsilon) = \varepsilon$ and $\Lambda(\hat p \boldsymbol p) = \Lambda(\boldsymbol p)\hat p\Lambda(\boldsymbol p)$, and the source turns such elements into finite words whose orbits are finite exactly when the element has finite order. Item 2 follows because a suffix-closed subset of an automaton semigroup or group is infinite iff it has an infinite orbit on some $\omega$-word, and item 3 by passing to the dual automaton. The refinement of Gillibert's construction, the infinite-orbit theorem for suffix-closed subsets and the duality between orbits and left ideals have no page.

## Sources

- Daniele D'Angeli, Dominik Francoeur, Emanuele Rodaro and Jan Philipp Wächter, "On the orbits of automaton semigroups and groups", *Algebra and Discrete Mathematics* 33(1), 2022, pp. 1–29, doi:[10.12958/adm1692](https://doi.org/10.12958/adm1692); read in arXiv:2007.10273v1 ([arXiv](https://arxiv.org/abs/2007.10273v1)), whose numbering is used: the abstract, Section 2 (preliminaries) and Section 3 (Theorem 3.1, Corollaries 3.2 and 3.3 and their proofs).
