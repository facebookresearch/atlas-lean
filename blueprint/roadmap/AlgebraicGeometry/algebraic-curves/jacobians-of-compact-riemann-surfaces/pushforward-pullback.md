# Pushforward of a pullback is multiplication by the degree

Let $X$ and $Y$ be compact
Riemann surfaces, that is, compact, connected, Hausdorff complex-analytic manifolds of dimension
one, and write $J(Y)$ for the Jacobian of $Y$, an abelian group. For every holomorphic map
$f : X \to Y$ and every $P \in J(Y)$, the pushforward along $f$ of the pullback of $P$ along $f$
is $\deg(f) \cdot P$, where the degree $\deg(f)$ is a natural number:
$f_*(f^*(P)) = \deg(f) \cdot P$.

## Sources

- https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`.
