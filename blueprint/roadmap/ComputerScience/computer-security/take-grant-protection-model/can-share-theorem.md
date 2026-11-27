# Characterization of can·share in the take–grant model

**Theorem (Lipton and Snyder).** Let $x$ and $y$ be vertices of a [protection graph](take-grant-protection-graphs.md) $G_0$ and $\alpha \subseteq R$. Then
[$\mathrm{can{\cdot}share}(\alpha, x, y, G_0)$](can-share-predicate.md) holds if and only if $G_0$ has an edge from $x$ to $y$ labelled $\alpha$, or the following hold
simultaneously:

1. there is a vertex $s$ of $G_0$ with an edge from $s$ to $y$ labelled $\alpha$;
2. there is a subject $x'$ such that $x' = x$ or $x'$ [initially spans](tg-paths-islands-spans-and-bridges.md) to $x$;
3. there is a subject $s'$ such that $s' = s$ or $s'$ terminally spans to $s$;
4. there are islands $I_1, \dots, I_n$ such that $x' \in I_1$, $s' \in I_n$ and for each $1 \le j < n$ there is a bridge from $I_j$ to $I_{j+1}$.

Here "labelled $\alpha$" means that the label contains $\alpha$, as in the definition of can·share.

## Depends on

- [The can·share predicate](can-share-predicate.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)
- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, Theorem 1 (credited there to R. J. Lipton and L. Snyder, "A linear time algorithm for deciding subject security", *Journal of the ACM* 24(3):455–464, 1977).
