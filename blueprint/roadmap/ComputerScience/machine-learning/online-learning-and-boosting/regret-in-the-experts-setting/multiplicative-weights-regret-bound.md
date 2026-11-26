# Regret of multiplicative weights: $\eta \sum |\ell| + \ln n/\eta$ and $2\sqrt{T \ln n}$ at every horizon

Let $X$ be a finite set of $n$ experts and run multiplicative weights with rate $\eta$.

1. If all losses lie in $[-1,1]$ and $0 < \eta \le 1/2$, then for every expert $i$ and horizon $T$,
$\sum_{t<T} \langle p_t, \ell_t\rangle \le \sum_{t<T} \ell_t(i) + \eta \sum_{t<T} |\ell_t(i)| + \frac{\ln n}{\eta}$.
2. If all losses lie in $[0,1]$, then for every horizon $T \ge 1$ the capped rate $\eta = \min\{\sqrt{\ln n / T}, 1/2\}$ gives external regret at most $2\sqrt{T \ln n}$ against every expert, with no lower restriction on $T$.

On binary losses the update is randomized weighted majority, so the second item contains the tuned randomized weighted majority bound.

## Proof sketch

The potential $W_t = \sum_i w_t(i)$ satisfies $W_{t+1} = W_t(1 - \eta\langle p_t, \ell_t\rangle)$, so $\ln W_T \le \ln n - \eta L^T$ by $\ln(1-x) \le -x$. Lower-bound $\ln W_T \ge \sum_t \ln(1 - \eta \ell_t(i)) \ge -\eta\sum_t \ell_t(i) - \eta^2 \sum_t \ell_t(i)^2$ for $\eta|\ell| \le 1/2$. For item 2, when $T < 4\ln n$ the cap $\eta = 1/2$ is used and the trivial bound $T \le 2\sqrt{T\ln n}$ applies.

## Depends on

- [Multiplicative weights (polynomial weights) algorithm](polynomial-weights-algorithm.md)

## Sources

- Sanjeev Arora, Elad Hazan and Satyen Kale, "The Multiplicative Weights Update Method: a Meta-Algorithm and Applications", Theory of Computing 8, 2012.
- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
