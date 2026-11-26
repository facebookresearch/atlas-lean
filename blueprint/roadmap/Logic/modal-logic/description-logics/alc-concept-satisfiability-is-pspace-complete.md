# ALC concept satisfiability is PSPACE-complete

The problem of deciding whether an ALC concept is satisfiable with respect to the empty TBox, in the sense of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md), is complete for [PSPACE](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md) under [polynomial-time many-one reductions](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md).

**Proof idea.** Membership: explore the tree model depth first, nondeterministically choosing disjuncts and keeping only one path of the tree with the direct successors of its individuals, which needs polynomial space; NPSPACE = PSPACE. Hardness: a reduction from the validity of quantified Boolean formulas.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Finite tree model property of ALC](finite-tree-model-property-of-alc.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../../TheoryOfComputation/complexity-classes/savitch.md)
- [TQBF is PSPACE-complete](../../../TheoryOfComputation/completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 3.1, the polynomial-space algorithm and Theorem 2, pp. 9–10, citing M. Schmidt-Schauß and G. Smolka (1991) and J. Y. Halpern and Y. Moses (1992) for hardness.
