# The can·share predicate

Let $x$ and $y$ be vertices of a [protection graph](take-grant-protection-graphs.md) $G_0$ and let $\alpha \subseteq R$ be a set of rights. The predicate
$\mathrm{can{\cdot}share}(\alpha, x, y, G_0)$ holds if and only if there are protection graphs $G_1, \dots, G_n$ such that $G_0 \vdash^* G_n$ using only the de jure
rules (take, grant, create and remove) and $G_n$ has an edge from $x$ to $y$ whose label contains $\alpha$.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, the definition of the predicate can·share.
