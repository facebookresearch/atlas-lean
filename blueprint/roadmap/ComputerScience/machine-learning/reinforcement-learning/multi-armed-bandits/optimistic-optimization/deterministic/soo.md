# Simultaneous optimistic optimization (SOO)

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a set $\mathcal X$ with
branching factor $K$, let $f \colon \mathcal X \to \mathbb{R}$, and let $h_{\max} \colon \mathbb{N} \to \mathbb{N}$, the
*depth function*. SOO with budget $n \ge 1$ starts from the [exploration tree](../exploration-trees.md)
$T = \{(0, 0)\}$ and the number of expansions $t = 0$, and repeats *sweeps* until $t = n$. A sweep does the following.

1. Set $v_{\max} = -\infty$ and $h_{\mathrm{top}} = \min(\operatorname{depth}(T), h_{\max}(t))$, for the current $T$
   and $t$.
2. For $h = 0, 1, \dots, h_{\mathrm{top}}$, in this order: if $T$ has leaves of depth $h$, choose one, $(h, i)$, whose
   value $f(x_{h,i})$ is the largest among them; if $f(x_{h,i}) \ge v_{\max}$, expand it, set $v_{\max} = f(x_{h,i})$ and
   $t = t + 1$, and stop the sweep and the algorithm if $t = n$.

SOO then returns $x(n) = x_{h,i}$ for a node $(h, i)$ of $T$ whose value $f(x_{h,i})$ is the largest among the nodes of
$T$. Ties are broken arbitrarily: a *run* of SOO with budget $n$ is any sequence of choices that follows these rules
and performs $n$ expansions, and the results on SOO hold for every run. Once every node of depth at most
$h_{\max}(t)$ is expanded, sweeps expand nothing, and the algorithm makes no further expansion. When the depth
function is a constant $H$, SOO expands only nodes of depth at most $H$, so a run with budget $n$ exists only if
$n \le 1 + K + \dots + K^H$; for larger $n$ the results on such runs are vacuous.

Within a sweep, the expanded nodes have increasing depths and nondecreasing values: a leaf is expanded only if its value
is the largest among the leaves of its depth and at least the value of every node expanded before it in the sweep.
SOO uses neither a semi-metric nor the diameters of the cells. The idea of the sources is to expand at once every leaf
whose upper bound $f(x_{h,i}) + \sup_{x \in X_{h,i}} \ell(x_{h,i}, x)$ could be the largest for some semi-metric $\ell$;
its guarantees hold for every semi-metric that satisfies the assumptions of its [loss bound](loss-of-soo.md).

The sources count $t$ from $1$ and return when $t = n$; here $t$ is the number of expansions performed, and $n$ is the
number of expansions, as in the analysis of the sources. As in their pseudo-code
(`for h = 0 to min(depth(T_t), h_max(t))`), the range of depths of a sweep is fixed when the sweep starts.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Section 4.1 and Figure 2.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 4.1 and Figure 4.1.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Exploration trees](../exploration-trees.md)
