# The can·share predicate

Let $p$ and $q$ be distinct vertices of a [protection graph](take-grant-protection-graphs.md) $G_0$ and let $\alpha \in R = \{r, w, t, g\}$. The predicate
$\mathrm{can{\cdot}share}(\alpha, p, q, G_0)$ holds if and only if there are protection graphs $G_1, \dots, G_n$ such that $G_0 \vdash^* G_n$ using only the de jure
rules (Take, Grant, Create and Remove) and $G_n$ has an edge from $p$ to $q$ whose label contains $\alpha$. In particular $p$ can acquire de jure read access to $q$
exactly when $\mathrm{can{\cdot}share}(r, p, q, G_0)$ holds.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Section 4, the definition of can·share (p. 19) and the remark following Theorem 4.1 (p. 20).
