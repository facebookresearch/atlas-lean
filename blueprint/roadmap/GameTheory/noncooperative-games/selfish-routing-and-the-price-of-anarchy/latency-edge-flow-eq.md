# Wardrop equilibria have unique edge latencies

Suppose every latency function $\ell_e$ is nondecreasing on $[0, \infty)$. If $f$ and $g$ are Wardrop equilibria
feasible for the same demand, then $\ell_e(f_e) = \ell_e(g_e)$ for every edge $e$.

The proof adds the variational inequalities of $f$ and $g$:
$\sum_e (\ell_e(f_e) - \ell_e(g_e))(f_e - g_e) \le 0$, and every term is nonnegative by
monotonicity (edge flows of feasible flows are nonnegative), hence zero.

## Informally uses

- [Variational inequality for Wardrop equilibria](cost-le-sum-latency-mul-edge-flow.md): applied
  to $f$ and to $g$.

## Sources

- M. Beckmann, C. B. McGuire and C. B. Winsten, *Studies in the Economics of Transportation*, Yale University Press, 1956.
- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Lemma 2.9 (§2.4) for the uniqueness of the equilibrium cost; the equality of edge latencies is the
  standard monotonicity argument.
