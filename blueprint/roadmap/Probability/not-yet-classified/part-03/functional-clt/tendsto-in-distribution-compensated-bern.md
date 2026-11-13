# Martingale FCLT for the compensated Bernoulli counting process

If the counting
increments `ξ i` are i.i.d., `{0,1}`-valued with success probability `p ∈ (0,1)`, then the
compensated counting process `compensatedBernoulliStep n p ξ` converges in distribution in
the Skorokhod J1 topology on `D([0,1])` to `√(p(1-p)) • W`, where `W` is a continuous version
of Brownian motion. In law this is Brownian motion time-changed by `A t = p (1 - p) t`
(informally the limit of the predictable quadratic variations,
`tendsto_compensatedBernoulli_predictableQV`), by Brownian scaling. That scaling identity is
not formalized here.

The hypotheses Rebolledo's theorem would need for this example are checked separately
and are not used by this proof: `condExp_sq_increment_compensatedBernoulli` (conditional
variances; informally the predictable quadratic variation is the deterministic
`p (1-p) ⌊n t⌋ / n`) and `lindebergConditionTriangular_compensatedBernoulli` (jump control).

## Sources

- Billingsley (1999), Theorem 16.1 (Donsker in `D`), specialized to Bernoulli increments; Andersen–Borgan–Gill–Keiding (1993), §II.5 for the counting-process reading.
