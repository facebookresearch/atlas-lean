# With complete lists every stable matching is perfect

Let $M$ and $W$ be finite sets of the same size, every man with a strict total order of preference on $W$ and
every woman with one on $M$, and let every agent rank remaining single last. Then every stable matching with
singles matches every man (and so, the sides having equal size, every woman). Hence, in the stable marriage
problem, the rural hospitals theorem holds trivially.

Proof: the Gale–Shapley theorem gives a stable perfect matching, which is stable as a matching with singles
by the bridge; it matches every man, and the rural hospitals theorem transfers this to every stable
matching.

## Informally uses

- [Existence of stable perfect matchings](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/gale-shapley-exists-stable-matching-gene.md): a stable perfect matching exists.
- [Bridge to the stable marriage model](stable-with-singles-iff-stable-perfect-matching.md): it is stable as a matching with singles.
- [Rural hospitals theorem, marriage case: every stable matching matches the same men](rural-hospitals-same-men.md): its matched men are matched at every stable matching.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, Lemma 1 (marriage case), combined with D. Gale and L. S. Shapley, "College admissions and the stability of marriage", *American Mathematical Monthly* 69 (1962), 9–15, Theorem 1.
