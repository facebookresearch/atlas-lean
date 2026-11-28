# Generalized arc consistency

A constraint of any arity is generalized arc consistent (GAC, also called domain consistent) on given finite domains when every value left in the domain of each of its variables extends to an allowed tuple using values from the other domains. On binary constraints this is arc consistency.

Let $C$ be a constraint with scope $(X_1,\dots,X_k)$, $k\ge 1$, that is, a set of $k$-tuples of values, and let $D$ be a domain on the scope: a finite set $D(X_i)$ of values for each $i$. For domains $D,D'$ on the same scope write $D'\subseteq D$ when $D'(X_i)\subseteq D(X_i)$ for every $i$.

- A **support** for the value $v\in D(X_i)$ on $C$ in $D$ is a tuple $t\in C$ with $t_i=v$ and $t_j\in D(X_j)$ for every $j$.
- $C$ is **generalized arc consistent** on $D$ when every value $v\in D(X_i)$, for every $i$, has a support on $C$ in $D$.
- A CSP (finitely many variables with finite domains and finitely many constraints on them) is GAC when each of its constraints is GAC on the restriction of the domains to its scope.

When $k=2$ the definition says that both arcs $(X_1,X_2)$ and $(X_2,X_1)$ are arc consistent in the sense of [arc consistency for binary CSPs](../../../ComputerScience/heuristic-search-and-planning/ac-3-algorithm/arc-consistent.md).

Boundary conventions. If some $D(X_i)$ is empty then no value of any other variable has a support, so $C$ is GAC on $D$ only when every $D(X_j)$ is empty; that totally empty domain is vacuously GAC, and propagation algorithms report it as a *domain wipe-out* rather than as a consistent state. A value $v\in D(X_i)$ has a support exactly when $C$ restricted to $D$ with $D(X_i)$ replaced by $\{v\}$ has an allowed tuple.

**GAC closure.** For every $D_0$ there is a unique largest $D\subseteq D_0$ on which $C$ is GAC: if $C$ is GAC on $D_1\subseteq D_0$ and on $D_2\subseteq D_0$, it is GAC on the componentwise union $D_1\cup D_2$, because a support in $D_1$ or in $D_2$ is still a support in the union. Equivalently, the largest GAC subdomain keeps exactly the values of $D_0$ that have a support on $C$ in $D_0$. A GAC propagator for $C$ maps $D_0$ to this domain.

## Depends on

- [Arc consistency for binary CSPs](../../../ComputerScience/heuristic-search-and-planning/ac-3-algorithm/arc-consistent.md): the binary special case named in the statement.

## Proof depends on

None.

## Expansion

The two facts in the last paragraphs are immediate from the definition. For the union, take $v\in D_1(X_i)\cup D_2(X_i)$; a support $t$ found in $D_1$ (say) satisfies $t_j\in D_1(X_j)\subseteq (D_1\cup D_2)(X_j)$. For the description of the closure, let $S(X_i)$ be the set of $v\in D_0(X_i)$ supported in $D_0$; every component of a supporting tuple of such a $v$ is itself supported by the same tuple, so the tuple lies in $S$ and $C$ is GAC on $S$; conversely every GAC $D\subseteq D_0$ satisfies $D\subseteq S$ because supports in $D$ are supports in $D_0$. Bessiere, Hebrard, Hnich and Walsh describe the same object as the "(unique) maximal generalised arc consistent subdomain" that GAC algorithms such as GAC-Schema compute.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Definitions of constraint, support and GAC in §2 and the maximal GAC subdomain in §3.1 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Definition 1 (arc consistency for $n$-ary CSPs, generalized arc consistency), p. 363.
