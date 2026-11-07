# Collar neighborhood theorem (topological form)

Let $n \ge 1$ and let $M$ be a Hausdorff,
second-countable smooth ($C^\infty$) manifold with boundary modeled on the closed half-space
$\{x \in \mathbb{R}^n : x_1 \ge 0\}$, and let $\partial M$ be its boundary. Then there is an open
embedding $c : \partial M \times [0, 1) \to M$ such that $c(b, 0) = b$ for every $b \in \partial M$.

Proof: Local chart collars are glued by Brown's external-collar construction, following Hatcher,
*Algebraic Topology*, Proposition 3.42, and the locally finite extension of Connelly (1971).

## Sources

- M. Hirsch, Differential Topology, GTM 33; J. Lee, Introduction to Smooth Manifolds, 2nd ed.; Kosinski, Differential Manifolds; Lean states topological collar `IsOpenEmbedding` corollary for `EuclideanHalfSpace` model.
