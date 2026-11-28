# A round costs weight in proportion to the algorithm's loss, up to $\eta^2 / 8$

Let $n \ge 1$ experts have positive weights $w_i$, let the losses $\ell_i$ of one round lie in $[0, 1]$, and let $\eta \ge 0$. After the Hedge update $w_i' = w_i e^{-\eta \ell_i}$, the total weight satisfies $\sum_i w_i' \le \left(\sum_i w_i\right) \exp(-\eta \bar\ell + \eta^2/8)$, where $\bar\ell = \sum_i w_i \ell_i / \sum_i w_i$ is the algorithm's loss in that round.
