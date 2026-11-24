# Obstacle contact force multiplier

For real numbers `k`, `f` and `u`, the contact force multiplier is the signed quantity
`λ = f - k u`; the obstacle pushes on the body with the force `-λ` along increasing `u`, so
equilibrium reads `f - k u - λ = 0`. It is nonnegative at a
[solution of the contact variational inequality](complementarity-of-vi.md), where it is the
magnitude of the obstacle reaction.
