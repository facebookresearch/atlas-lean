# Bicriteria bound for selfish routing

Suppose every latency $\ell_e$ is nonnegative and nondecreasing on $[0, \infty)$. If $f$ is a
Wardrop equilibrium feasible for the demand $r$ and $g$ is feasible for the demand $(1 + \gamma) r$,
then $\gamma\, C(f) \le C(g)$.

For $\gamma > 0$ this is Roughgarden and Tardos's $C(f) \le C(g)/\gamma$; no sign condition on
$\gamma$ is needed (for $\gamma \le 0$ the statement is weaker than $C(g) \ge 0$). No
continuity is needed. The proof uses
$\ell_e(f_e)\, g_e \le \ell_e(g_e)\, g_e + \ell_e(f_e)\, f_e$ on every edge, which replaces
the modified latencies $\max(\ell_e(f_e), \ell_e(x))$ of the original argument.

## Informally uses

- [Wardrop flows against a scaled demand](smul-sum-path-latency-mul-le.md): with $c = 1 + \gamma$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Theorem 3.2.
