# Sufficient decrease of an exact trust-region step

If $s$ minimises the [quadratic model](trust-region-model.md) $q$ over the ball $\|p\| \le \Delta$
and $v^\top B v \le M \|v\|^2$ for all $v$, with $M > 0$, then

$$-q(s) \ge \tfrac12\, \|g\| \min\Bigl(\Delta, \frac{\|g\|}{M}\Bigr).$$

With $M = \|B\|$ (when $B \ne 0$) this is inequality (2.5) of the source for the exact solution of
the standard trust-region subproblem. Any approximate step inside the region whose model value is at
most that of the Cauchy step satisfies the same bound.

## Informally uses

- [Cauchy decrease of the trust-region model](exists-cauchy-step.md): the exact minimiser does at
  least as well as the steepest-descent step inside the region.

## Sources

- Y. Yuan, *Recent advances in trust region algorithms*, Math. Program. 151 (2015), 249–281; https://lsec.cc.ac.cn/pub/yyx/papers/2015-MPB-151-249-281.pdf, inequality (2.5).
