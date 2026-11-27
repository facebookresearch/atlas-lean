# Parity lifts characterize finite choices by Weisfeiler–Leman equivalence

Fix $k\ge4$. In the joint convention let $t=k+1$ and $r=2$; in the separate convention let $t=k$ and $r=1$. A choice system assigns each index $i<t$ a finite domain $D_i$, and each pair $i<j$ a finite label set with one map from each of $D_i,D_j$. Success is a domain choice at every $i$ with both labels equal for each pair. Form a template with a clique on the main indices and one independent helper vertex for each pair $i<j$ and third index $l\notin\{i,j\}$, adjacent to those three mains. The base graph replaces a main with its domain and a helper with its pair's labels; two main choices are adjacent precisely on matching labels, a helper label is adjacent to the matching choices at $i,j$, and it is adjacent to all choices at $l$.

A lift over each base vertex chooses a bit for each neighbor of its template vertex, with prescribed parity at that template vertex. A lifted pair is adjacent when the base pair is adjacent and their bits pointing at each other's template vertices coincide. Compare parity identically zero with parity one just at main index zero. The two uncolored lifts have equal vertex counts; if each domain and label set has size at most $A\ge1$, their order is at most $A(t2^{t-2+3\binom{t-1}{2}}+12\binom{t}{3})$.

Refinement initially colors each $k$-tuple by all equalities and adjacencies. Every update retains the old color and either the joint multiset, over vertices $z$, of color vectors for replacing each coordinate by $z$, or in the separate convention one multiset per coordinate. Equivalence is equality at all rounds of the tuple-color multisets. The pure version refines tuples inside the disjoint union and compares the all-first-component and all-second-component tuple multisets there. Both equivalences of the two lifts hold exactly when the choice system has no successful choice. If it has one, both histogram equalities already fail at round $r$.

## Depends on

- Finite labelled compatibility systems, the uncolored parity lifts under a template projection, and joint/separate plus ordinary/pure tuple refinement.

## Proof depends on

- Parity-coupling witness for no choice, detection at the specified round when there is one, and exact fiber counting.

## Expansion

Formalize the construction and fiber counts before round-by-round comparison. Separate ordinary refinement from the pure disjoint-union version, and check both successful-round bounds, noting the change in bag parameter. No conditional time exclusion follows in this selected statement alone.

## Sources

- [Comparator statement: `OAI.ParityWL.parity_reduction`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ParityLifts.lean#L204-L206)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/133.md)
