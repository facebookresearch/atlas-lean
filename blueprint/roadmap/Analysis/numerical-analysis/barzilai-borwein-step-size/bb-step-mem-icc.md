# Barzilai–Borwein steps on a quadratic lie between the inverse curvature bounds

Let $A$ be a linear operator with $m \|v\|^2 \le v^\top A v \le L \|v\|^2$ for all $v$, where
$m > 0$, and let $s \ne 0$. On the quadratic $f(x) = \tfrac12 x^\top A x - b^\top x$ the gradient change
along a step $s$ is $y = A s$, and the [first Barzilai–Borwein step](bb-step.md) satisfies

$$\frac1L \le \alpha = \frac{s^\top s}{s^\top A s} \le \frac1m :$$

$1/\alpha$ is the Rayleigh quotient of $A$ at $s$. This makes precise the remark of the source that
the step approximates the inverse of the second directional derivative of $f$ along $s$.

## Sources

- Y. H. Dai, J. Y. Yuan and Y. Yuan, *Modified two-point stepsize gradient methods for unconstrained optimization*, Comput. Optim. Appl. 22 (2002), 103–109; https://lsec.cc.ac.cn/pub/home/yyx/papers/daiyuanyuan.pdf, Section 2 (formula (2.1) and the remark after (2.5)).
