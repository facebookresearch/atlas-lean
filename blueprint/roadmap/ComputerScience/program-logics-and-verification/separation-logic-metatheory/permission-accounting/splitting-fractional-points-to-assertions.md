# Splitting and joining fractional points-to assertions

With fractional permissions, a points-to assertion with permission $q + q'$ is exactly the separating conjunction of the same assertion with permissions $q$ and $q'$, provided $q + q' \le 1$; and two fractional points-to assertions for the same address can hold separately only if they agree on its contents.

Work with heaps over the fractional permission model of [fractional and counting permission models](fractional-and-counting-permission-models.md), and read $E \overset{r}{\mapsto} E'$ as false when $r \notin (0, 1]$. For rationals $q, q' > 0$ and expressions $E, E', F, F'$, at every store and heap,

$$E \overset{q+q'}{\longmapsto} E' \iff \left(E \overset{q}{\mapsto} E' \ast E \overset{q'}{\mapsto} E'\right) \wedge q + q' \le 1,$$

$$E \overset{q}{\mapsto} F \ast E \overset{q'}{\mapsto} F' \implies F = F' \wedge q + q' \le 1,$$

where $F = F'$ means that both expressions have the same value in the current store.

Consequently $\ast$ no longer implies that the two heaps have disjoint domains: $E \overset{1/2}{\mapsto} F \ast E \overset{1/2}{\mapsto} F$ holds of the one-cell heap that holds the value of $F$ at the address $E$ with permission $1$.

## Depends on

- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Permission algebras and heaps with permissions](permission-models.md)

## Proof depends on

- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Permission algebras and heaps with permissions](permission-models.md)

## Expansion

For the tree predicate obtained by decorating every points-to of the source's tree predicate (its equations (21)–(22), with $\mathrm{ztree}\,z\,t\,\tau$ the tree predicate for root $t$ and abstract tree $\tau$ whose points-to assertions all carry permission $z$) with the same fraction $z$, the law $\mathrm{ztree}\,(z + z')\,t\,\tau \iff \mathrm{ztree}\,z\,t\,\tau \ast \mathrm{ztree}\,z'\,t\,\tau$ holds, with the same root $t$ and the same abstract tree $\tau$ in all three assertions; but the two halves may describe overlapping structures, so such predicates need not describe disjoint substructures. Let $l = [\![E]\!]s$ and $v = [\![E']\!]s$. The left-hand side of the first law holds exactly of the heap $[l \mapsto (v, q + q')]$, which exists only when $q + q' \le 1$. A heap satisfies the separating conjunction exactly when it is $[l \mapsto (v, q)] \circ [l \mapsto (v, q')]$, which is defined if and only if $q \star_2 q'$ is defined, that is $q + q' \le 1$, and then equals $[l \mapsto (v, q + q')]$. For the second law, $[l \mapsto (w, q)] \circ [l \mapsto (w', q')]$ is defined only when $w = w'$ and $q + q' \le 1$, by the lifting of $\star$ to value–permission pairs. The tree remark is the source's observation that the splitting law sometimes holds only vacuously; the share-model view is that fractions violate the disjointness axiom of [positivity, disjointness and cross-split](positivity-disjointness-and-cross-split.md).

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 10.3, equation (17); Section 10.1 (combination agrees on values); Section 13.1 (fractionally decorated trees, equations (21) and (22), and the loss of disjointness of domains).
- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 6, equation (35) and the remark after Definition 8 (equation numbers of the author copy).
