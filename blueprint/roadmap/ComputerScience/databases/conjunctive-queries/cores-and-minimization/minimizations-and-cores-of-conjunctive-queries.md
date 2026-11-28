# Minimizations and cores of conjunctive queries

Let $q(\bar x)$ be a conjunctive query over a schema $\mathbf S$, possibly with constants. A conjunctive query $q'$ over
$\mathbf S$ is a *minimization* of $q$ when $q' \equiv q$ and every conjunctive query $q''$ over $\mathbf S$ with
$q'' \equiv q'$ has at least as many body atoms as $q'$.

A conjunctive query $q'(\bar x)$, with the same head tuple $\bar x$, is a *core* of $q$ when

1. $A_{q'} \subseteq A_q$,
2. $(q, \bar x) \to (q', \bar x)$, and
3. no conjunctive query $q''(\bar x)$ with $A_{q''} \subsetneq A_{q'}$ satisfies $(q', \bar x) \to (q'', \bar x)$.

Here a conjunctive query $q''(\bar x)$ with a given body requires every variable of $\bar x$ to occur in that body.
Conditions 1 and 2 give $q' \equiv q$; condition 3 says that no atom can be dropped from $q'$ by a homomorphism that
fixes the head. For example, $\mathrm{Answer} \mathrel{:-} R(x, y)$ and $\mathrm{Answer} \mathrel{:-} R(x, z)$ are both cores
of the Boolean query $\mathrm{Answer} \mathrel{:-} R(x, y), R(x, z)$.

## Depends on

- [Containment, equivalence and homomorphisms of conjunctive queries](containment-equivalence-and-homomorphisms-of-conjunctive-queries.md)

## Proof depends on

- [Homomorphism theorem for conjunctive queries with constants](homomorphism-theorem-for-conjunctive-queries-with-constants.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 16.1 and 16.2 and Example 16.3 (pp. 123–125).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 6.2 (tableau minimization, Theorem 6.2.6, p. 118).
