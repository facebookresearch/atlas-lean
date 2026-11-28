# Top-k choice among a finite set

Let $f$ assign to each object a score in a linearly ordered
set, let $k \in \mathbb{N}$ and let $S$ be a finite set of objects. A set $B$ is a top-$k$ choice
among $S$ for $f$ when $B \subseteq S$, $B$ has $\min(k, |S|)$ elements, and $f(z) \le f(y)$ for
every $y \in B$ and every $z \in S \setminus B$. So $B$ consists of $k$ elements of $S$ of highest
score, or of all of $S$ when $|S| \le k$; ties may be resolved either way.
