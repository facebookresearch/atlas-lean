# Priced Wardrop equilibrium with reservation utility

Consider parallel links $i$ with continuous nondecreasing latencies $\ell_i$ and per-unit prices $p_i \ge 0$, a mass $d$ of nonatomic users each with reservation utility $R$. A flow $x \ge 0$ with $\sum_i x_i \le d$ is a *priced Wardrop equilibrium* if every used link has minimal effective cost $\ell_i(x_i) + p_i$, this minimal cost is at most $R$, and if $\sum_i x_i < d$ then the minimal effective cost equals $R$ (users decline to transmit only when indifferent). The social surplus of $x$ is $R \sum_i x_i - \sum_i x_i \ell_i(x_i)$, consumer surplus subtracts payments, and provider profit is $\sum_i p_i x_i$.

## Depends on

- [Wardrop equilibrium](../is-wardrop.md)
- [Nonatomic routing instance](../routing-instance.md)

## Sources

- Asuman Ozdaglar and R. Srikant, "Incentives and Pricing in Communications Networks", Algorithmic Game Theory, Cambridge University Press, 2007.
- Daron Acemoglu and Asuman Ozdaglar, "Competition and Efficiency in Congested Markets", Mathematics of Operations Research, 2007.
