# Cauchy decrease of the trust-region model

Let $\Delta \ge 0$ and $M > 0$, and suppose $v^\top B v \le M \|v\|^2$ for all $v$ (for instance
$\|B\| \le M$). Then some step $s = -t g$ along the steepest-descent direction, with $t \ge 0$ and
$\|s\| \le \Delta$, has predicted reduction

$$-q(s) \ge \tfrac12\, \|g\| \min\Bigl(\Delta, \frac{\|g\|}{M}\Bigr)$$

for the [quadratic model](trust-region-model.md) $q(s) = g^\top s + \tfrac12 s^\top B s$. This is
Powell's sufficient model decrease, the inequality on which the global convergence of trust-region
methods rests; the source states it with $M = \|B\|$ and notes that the minimiser of the model
along $-g$ inside the trust region satisfies it.

Proof: take $t = \min(\Delta / \|g\|, 1/M)$. Then $\|s\| = t\|g\| \le \Delta$ and
$q(s) = -t\|g\|^2 + \tfrac12 t^2 g^\top B g \le -t\|g\|^2 + \tfrac12 t (tM) \|g\|^2 \le -\tfrac12 t \|g\|^2$,
while $t\|g\| = \min(\Delta, \|g\|/M)$.

## Sources

- Y. Yuan, *Recent advances in trust region algorithms*, Math. Program. 151 (2015), 249–281; https://lsec.cc.ac.cn/pub/yyx/papers/2015-MPB-151-249-281.pdf, inequality (2.5) and the remark after it (credited there to Powell).
