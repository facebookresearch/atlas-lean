# The marginal law of the hierarchy is negative binomial

For `a > 0`, `b > 0`, `s ≥ 0` and every `k ∈ ℕ`, the [marginal likelihood](marginal-lik.md) of `k`
equals the
[negative binomial mass](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)
`NB(k; a, s a / b) = a⁽ᵏ⁾ / k! · (b / (b + s))^a (s / (b + s))^k` with size `a` and mean `s a / b`,
where `a⁽ᵏ⁾` is the rising factorial: the Greenwood–Yule mixture with exposure `s`.

## Sources

- M. Greenwood and G. U. Yule, *An inquiry into the nature of frequency distributions representative
  of multiple happenings*, J. Roy. Statist. Soc. 83 (1920), 255–279.
