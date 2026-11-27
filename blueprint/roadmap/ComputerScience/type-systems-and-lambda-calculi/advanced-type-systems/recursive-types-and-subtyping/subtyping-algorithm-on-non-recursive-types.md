# The subtyping algorithm on μ-free types

For μ-free types $\alpha$ and $\beta$, [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) succeeds on $\alpha \le \beta$ if and only if $\alpha \le_T \beta$ in the
[tree ordering](tree-ordering-on-recursive-types.md), which on μ-free types is the inductively generated subtyping. Both directions are by induction on $\alpha$ and $\beta$,
using that assumptions may be added to or dropped from the trail, and equations to or from the system, when they are not reachable from the current goal
(adding equations requires their domain to be disjoint from the system's, and adding assumptions requires the trail to remain valid for the system).

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)

## Proof depends on

- [Canonical forms and regular systems of equations](canonical-forms-and-regular-systems-of-equations.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.3, Lemma 4.3.1 (derived structural rules) and Propositions 4.3.2 and 4.3.3 (completeness and soundness for non-recursive types).
