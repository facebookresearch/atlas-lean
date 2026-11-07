# Erdős Problem 754: favourite distances in $\mathbb{R}^4$

There is a real constant $C$ such
that for every nonempty finite set $A$ of points of the Euclidean space $\mathbb{R}^4$ and every
natural number $f$, if for every $x \in A$ there is a real number $r > 0$ such that at least $f$
points of $A$ lie at distance $r$ from $x$, then $f \le |A|/2 + C$.

Swanepoel proved that for every finite $A \subseteq \mathbb{R}^4$ with $|A| = n$ and every choice
of distances $r(x) > 0$, the number of pairs $(x, y)$ of points of $A$ with $|x - y| = r(x)$ is at
most $n^2/2 + O(n)$, which gives this bound.

## Sources

- T. F. Bloom, Erdős Problems, Problem #754, https://www.erdosproblems.com/754 (status PROVED (LEAN)); resolution: K. J. Swanepoel, Favourite distances in high dimensions, Thirty Essays on Geometric Graph Theory (2013), 499-519, abstract of arXiv:1108.4817: f_d(n) = max ∑_{x ∈ S} e_r(x, S) = (1 - 1/⌊d/2⌋) n² + Θ(n) for even d (n²/2 + O(n) for d = 4); erdosproblems.com/754: proved by Swanepoel (Avis, Erdős and Pach had n/2 + 2 ≤ f(n) ≤ (1 + o(1)) n/2), https://arxiv.org/abs/1108.4817.
