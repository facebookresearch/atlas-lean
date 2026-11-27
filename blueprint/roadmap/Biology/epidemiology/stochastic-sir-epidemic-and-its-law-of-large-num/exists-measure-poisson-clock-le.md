# A $C/N$ bound in the uniform law of large numbers for Poisson clocks

Let $(\Omega, P)$ be a probability space, $B$ real and $\eta > 0$. There is a real constant $C$,
not depending on $Y$ or $N$, such that for every unit-rate
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) $Y$ on $(\Omega, P)$ and every natural number $N \ge 1$,

$$P\left(\exists\, a \in [0, B],\ \left|Y(N a)/N - a\right| > \eta\right) \le \max(C/N, 0).$$

The event is $\{\sup_{a \in [0, B]} |Y(N a)/N - a| > \eta\}$, empty when $B < 0$. It is not
assumed measurable, and $P$ is applied to it as an outer measure. Replacing $C$ by $\max(C, 0)$,
the bound is $C/N$ with $C \ge 0$.

Proof: on the grid $a_k = k \eta / 4$ ($k \le \lceil 4 B / \eta \rceil + 1$) Chebyshev's inequality
bounds the probability of each event $|Y(N a_k) / N - a_k| \ge \eta / 2$; off the union of these
events (and the null event where $Y$ is not a nondecreasing path from $0$) monotonicity of $Y$
squeezes $Y(N a) / N$ between two consecutive grid values, which keeps it within $3 \eta / 4$ of
$a$.
