# Total weight bound for the Hedge algorithm

Let $n \ge 1$ experts start from positive weights $w_i$, let $\eta \ge 0$, and let a sequence of $T$ rounds have all losses in $[0, 1]$. Then the total weight after the $T$ Hedge updates is at most $\left(\sum_i w_i\right) \exp(-\eta L + T \eta^2/8)$, where $L$ is the algorithm's cumulative loss over the $T$ rounds.
