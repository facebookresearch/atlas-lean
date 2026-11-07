# Universal property of the Jacobian

Let $C$ be a proper, smooth, geometrically irreducible
curve over a field $k$, let $J(C)$ be its Jacobian, let $P$ be a $k$-rational point of $C$, and
let $\iota_P : C \to J(C)$ be the Abel–Jacobi map based at $P$. Let $A$ be a group scheme over $k$
that is smooth, proper and geometrically irreducible. For every morphism of $k$-schemes
$f : C \to A$ sending $P$ to the identity point of $A$, there is a unique morphism of $k$-schemes
$g : J(C) \to A$ with $f = g \circ \iota_P$.

In other words, the Jacobian of $C$ is the Albanese variety of $C$.

## Sources

- https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685. Problem `jacobian_challenge_alggeo` of the lean-eval benchmark.
