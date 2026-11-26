# Characterization of can·share in the take–grant model

**Theorem (Jones, Lipton and Snyder).** Let $p$ and $q$ be distinct vertices of a [protection graph](take-grant-protection-graphs.md) $G_0$ and $\alpha \in \{r, w, t, g\}$.
Then [$\mathrm{can{\cdot}share}(\alpha, p, q, G_0)$](can-share-predicate.md) holds if and only if either $G_0$ has an edge from $p$ to $q$ whose label contains
$\alpha$, or the following hold simultaneously:

1. there is a vertex $s$ of $G_0$ with an edge from $s$ to $q$ whose label contains $\alpha$;
2. there are subjects $p'$ and $s'$ such that $p'$ initially spans to $p$ and $s'$ terminally spans to $s$;
3. there are [islands](tg-paths-islands-spans-and-bridges.md) $I_1, \dots, I_v$ with $p' \in I_1$ and $s' \in I_v$, and for each $1 \le j < v$ a bridge from a vertex of
   $I_j$ to a vertex of $I_{j+1}$.

These conditions can be tested in time linear in the size of $G_0$, so the safety question "can $p$ ever obtain the right $\alpha$ to $q$" is decidable in linear
time in the take–grant model, in contrast with [the general access-matrix model](../access-control/safety-is-undecidable-for-protection-systems.md).

## Depends on

- [The can·share predicate](can-share-predicate.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Theorem 4.1 (p. 19, with the correction written on the copy: the alternative of an edge from $p$ to $q$ labelled $\alpha$ in $G_0$, and $p' \in I_1$, $s' \in I_v$) and the remark on linear-time testing that follows it; the theorem is credited there to Jones, Lipton and Snyder (FOCS 1976) and Lipton and Snyder (*J. ACM* 24(3), 1977).
