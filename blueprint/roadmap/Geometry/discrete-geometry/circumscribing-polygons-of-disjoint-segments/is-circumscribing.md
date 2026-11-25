# Circumscribing polygons of a segment family

Let $e_0, \dots, e_{2m-1} \in \mathbb{R}^2$ be the endpoints of segments $s_k = [e_{2k}, e_{2k+1}]$, $k = 0, \dots, m-1$, and let $\pi$ be a permutation of $\{0, \dots, 2m - 1\}$, giving the closed polygon $e_{\pi(0)} e_{\pi(1)} \cdots e_{\pi(2m-1)}$ through all endpoints (indices of $\pi$ taken mod $2m$). The polygon is circumscribing when there is a set $K \subseteq \mathbb{R}^2$ that is compact, has nonempty interior, and has frontier equal to the union of the polygon's edges $[e_{\pi(t)}, e_{\pi(t+1)}]$, such that every segment $s_k$ is

- an edge of the polygon, that is, $\{\pi(t), \pi(t+1)\} = \{2k, 2k+1\}$ for some $t$; or
- an internal chord, that is, the open segment $(e_{2k}, e_{2k+1})$ lies in the interior of $K$.

So no segment lies outside the polygon.
