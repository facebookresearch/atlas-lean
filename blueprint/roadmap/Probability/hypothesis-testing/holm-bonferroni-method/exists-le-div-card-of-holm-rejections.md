# Holm rejection bound for a set of hypotheses

Let $m \in \mathbb{N}$, $\alpha \ge 0$, $p_0, \dots, p_{m-1} \in \mathbb{R}$ and $J \subseteq \{0, \dots, m-1\}$. If Holm's procedure at level $\alpha$ rejects some hypothesis in $J$, then some $j \in J$ has $p_j \le \alpha/|J|$: the first hypothesis of $J$ in sorted order sits at a position $k \le m - |J| + 1$. This bound is used both for [Holm's familywise error control](measure-holm-familywise-error-le.md) and for identifying Holm's procedure with the closure of the Bonferroni local tests.
