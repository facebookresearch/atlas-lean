# Adaptive consistency via bucket elimination

Let a finite constraint network have variables $X_1, \dots, X_n$ with finite domains of size at most
$k$ and $m$ constraints, each given as a table on its scope, and fix an ordering $d$ of the variables
with induced width $w^*(d)$ of the primal graph. Bucket elimination with relational join and
projection, processing the variables from last to first:

1. decides satisfiability: the network has a solution if and only if the final relation on the empty
   scope is nonempty;
2. if the network is satisfiable, assigning $X_1, \dots, X_n$ in order, each to a value consistent with
   the earlier values and with every relation in its bucket, never needs to backtrack;
3. performs $O\bigl((m + n)\, k^{w^*(d) + 1}\bigr)$ tuple operations, since every relation it creates
   has scope of size at most $w^*(d) + 1$.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: constraint networks with finite domains and constraints of arbitrary arity given as relations (tables) on their scopes, with their primal (constraint) graph.

## Depends on

- [Induced width of an ordering](../../machine-learning/probabilistic-graphical-models/induced-width-of-an-ordering.md)

## Proof depends on

- [Bucket elimination over a commutative semiring](../../machine-learning/probabilistic-graphical-models/bucket-elimination-over-a-commutative-semiring.md)

## Sources

- R. Dechter, *Bucket elimination: a unifying framework for reasoning*, Artificial Intelligence 113 (1999) 41–85, Section 2: algorithm Adaptive-consistency (Fig. 3, p. 45) and Theorems 1 and 2 (p. 46). Theorem 2 gives $O(n \exp(w^*(d)))$ with domain size and number of constraints held fixed; the bound above makes both explicit. <http://ics.uci.edu/~dechter/publications/r76A.pdf>
