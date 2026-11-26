# Self-consistency

For [grouped right-censored data](censored-data.md) with sample size $n$ and every $t \in \mathbb{R}$,

$$n\, \hat S(t) = \sum_{j : t_j > t} (d_j + c_j) + \sum_{j : t_j \le t} c_j\, \frac{\hat S(t)}{\hat S(t_j)}:$$

$n\hat S(t)$ is the number of observations exceeding $t$ plus, for each subject censored at or before $t$, the conditional survival $\hat S(t)/\hat S(t_j)$ (with the ratio read as $0$ when $\hat S(t_j) = 0$).

## Sources

- Bradley Efron, *The two sample problem with censored data*, Proc. Fifth Berkeley Symp. Math. Statist. Probab., Vol. 4 (1967), 831–853, equation (7.4).
