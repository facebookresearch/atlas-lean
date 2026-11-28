# A generalized finiteness problem for automaton groups is undecidable

There is an automaton group for which no algorithm decides, given a finite word $w$, whether the set of sections of the group elements at $w$ is finite; this generalized finiteness problem for automaton groups is equivalent to finiteness of left principal ideals in semigroups of complete reversible automata.

Let $\mathcal T = (Q, \Sigma, \delta)$ range over G-automata (complete, deterministic and inverse-deterministic synchronous automata), whose states generate an [automaton group](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group.md) $\mathscr G(\mathcal T)$ acting on $\Sigma^*$ and $\Sigma^\omega$ by $g \circ w$, and complete reversible S-automata, generating automaton semigroups $\mathscr S(\mathcal T)$ (see [automaton semigroups and monoids](automaton-semigroups.md)). For a word $w$, finite or infinite, its *orbit* $Q^* \circ w$ is the set of its images under all products of states. For $g \in \mathscr G(\mathcal T)$ and $w \in \Sigma^*$, the *section* $g \cdot w \in \mathscr G(\mathcal T)$ is the element with $g \circ (wv) = (g \circ w)\,((g \cdot w) \circ v)$ for all $v \in \Sigma^*$ (the source's right action of words on state sequences, Section 2). The orbit of a finite word is always finite, since it lies in $\Sigma^{|w|}$; the set of sections $\mathscr G(\mathcal T) \cdot w = \{g \cdot w : g \in \mathscr G(\mathcal T)\}$ need not be.

**Theorem (D'Angeli, Francoeur, Rodaro and Wächter).**

1. There is a G-automaton $\mathcal T = (Q, \Sigma, \delta)$ such that it is undecidable, given $w \in \Sigma^*$, whether the set of sections $\mathscr G(\mathcal T) \cdot w$ is finite (Theorem 3.1); equivalently, in the source's introduction, whether there are infinitely many state sequences whose actions differ pairwise on all words with prefix $w$.
2. For such a $\mathcal T$, it is undecidable, given $w \in \Sigma^*$, whether some $\omega$-word $\alpha \in \Sigma^\omega$ makes the orbit $Q^* \circ w\alpha$ infinite (Corollary 3.2).
3. There is a complete reversible S-automaton $\mathcal R = (P, \Gamma, \tau)$ such that it is undecidable, given $\boldsymbol p \in P^*$, whether the left principal ideal $P^* \boldsymbol p$ of $\mathscr S(\mathcal R)$ is finite (Corollary 3.3; $\mathcal R$ is the dual of the automaton of item 1).

The source presents item 1 as a more general version of the finiteness problem for automaton groups (given a G-automaton $\mathcal T$, is $\mathscr G(\mathcal T)$ finite?), the case $w = \varepsilon$, since $\mathscr G(\mathcal T) \cdot \varepsilon = \mathscr G(\mathcal T)$; whose decidability is an open question; the finiteness problem for automaton semigroups is undecidable (Gillibert).

## Depends on

- [Automaton semigroups and monoids](automaton-semigroups.md)
- [Automaton group](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some automaton group has undecidable order problem](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group-undecidable-order-problem.md)

## Expansion

Item 1 uses Gillibert's construction of an automaton group with undecidable order problem: his proof actually shows that it is undecidable whether an element of the special form $\diamond\Lambda(\boldsymbol p)$ has finite order, for a fixed state $\diamond$ (written as a dollar sign in the source), with $\Lambda(\varepsilon) = \varepsilon$ and $\Lambda(\hat p \boldsymbol p) = \Lambda(\boldsymbol p)\hat p\Lambda(\boldsymbol p)$, and the source turns such elements into finite words whose sets of sections are finite exactly when the element has finite order. Item 2 follows because a suffix-closed subset of an automaton semigroup or group is infinite iff it has an infinite orbit on some $\omega$-word, and item 3 by passing to the dual automaton. A good expansion links pages for the refinement of Gillibert's construction, the infinite-orbit theorem for suffix-closed subsets (Theorem 2.5 of the source) and the duality between orbits and left ideals (Corollary 2.8).

## Sources

- Daniele D'Angeli, Dominik Francoeur, Emanuele Rodaro and Jan Philipp Wächter, "On the orbits of automaton semigroups and groups", *Algebra and Discrete Mathematics* 33(1), 2022, pp. 1–29, doi:[10.12958/adm1692](https://doi.org/10.12958/adm1692); read in arXiv:2007.10273v1 ([arXiv](https://arxiv.org/abs/2007.10273v1)), whose numbering is used: the abstract, Section 2 (preliminaries, including Theorems 2.4 and 2.5 and Corollary 2.8) and Section 3 (Theorem 3.1, Corollaries 3.2 and 3.3 and their proofs).
