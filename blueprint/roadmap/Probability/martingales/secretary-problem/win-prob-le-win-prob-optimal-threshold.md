# The optimal threshold rule of the secretary problem

Let $n \ge 1$ and $1 \le r \le n$. Then the [win probability](win-prob.md) of the threshold rule
$N_r$ satisfies $P_r \le P_{r_1}$, where
$r_1 = \min\{r \ge 1 : \sum_{k=r+1}^{n} 1/(k - 1) \le 1\}$ is the [optimal
threshold](optimal-threshold.md): $r_1$ maximises $P_r$ over $1 \le r \le n$.

The proof is Ferguson's: the tail $T_r$ decreases in $r$, so the increments $P_{r+1} - P_r = (T_r - 1)/n$ are positive before $r_1$ and nonpositive from $r_1$ on. This optimises over threshold rules only; that no rank-based rule does better is [the optimality of the threshold rule among all rank-based rules](card-rank-rule-wins-div-factorial-le.md).

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics), Chapter 2, §2.1, equations (3)–(4).

## Informally uses

- [Increment of the win probability of threshold rules](win-prob-succ-sub.md)
