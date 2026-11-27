# Weak haploid selection follows the logistic curve on the time scale 1/s

For genic selection with coefficient $s > 0$, let $x_{t+1} = x_t (1 + s)/(1 + s x_t)$ with $x_0 \in (0, 1)$, and let
$X(\tau)$ be the [logistic solution](../../detecting-selection/selective-sweeps/sweep-traj.md) of
$X' = s X (1 - X)$ with $X(0) = x_0$. Then, writing $\operatorname{logit} x = \log(x/(1 - x))$,

$$\operatorname{logit} x_t = \operatorname{logit} x_0 + t \log(1 + s), \qquad \operatorname{logit} X(t) = \operatorname{logit} x_0 + s t,$$

and for every $T > 0$

$$\sup_{t \in \mathbb N,\ 0 \le t \le T/s} |x_t - X(t)| \le \frac{T s}{8} .$$

The first identity is the [log-odds growth under repeated haploid selection](log-odds-iterate-select.md)
with fitness ratio $1 + s$. The bound follows from $0 \le s - \log(1 + s) \le s^2/2$, which gives a logit difference
at most $t s^2 / 2 \le T s / 2$ for $t \le T/s$, and from the logistic function $y \mapsto 1/(1 + e^{-y})$ being
$\tfrac14$-Lipschitz. In particular the discrete recursion converges to the logistic curve uniformly on time
windows of length of order $1/s$ as $s \to 0$.

## Depends on

- [Logistic sweep trajectory](../../detecting-selection/selective-sweeps/sweep-traj.md)

## Proof depends on

- [Log-odds under repeated haploid selection](log-odds-iterate-select.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.6 (rates of change of gene frequency; replacing $1 + s$ by $e^{r_A - r_a}$ turns the discrete-generation formula into the continuous-generation one). The bound is derived above.
