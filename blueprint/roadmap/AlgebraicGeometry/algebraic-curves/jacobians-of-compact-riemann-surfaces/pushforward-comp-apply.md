# Pushforward respects composition

Let $X$, $Y$ and $Z$ be compact Riemann surfaces, that
is, compact, connected, Hausdorff complex-analytic manifolds of dimension one, and write $J(X)$
for the Jacobian of $X$. For all holomorphic maps $f : X \to Y$ and $g : Y \to Z$ and every
$P \in J(X)$, the pushforwards satisfy $(g \circ f)_*(P) = g_*(f_*(P))$.

## Sources

- https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge. Problem `jacobian_challenge_diffgeo` of the lean-eval benchmark.
