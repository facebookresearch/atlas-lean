# Relations between STAT and VSTAT oracles and their simulation from samples

Let STAT$(\tau)$ answer a query $h : \mathcal{X} \to [0,1]$ with any $v$ satisfying $|v - \mathbb{E}_D[h]| \le \tau$. Then every valid answer of VSTAT$(t)$ is a valid answer of STAT$(1/\sqrt{t})$, and every valid answer of STAT$(1/t)$ is a valid answer of VSTAT$(t)$; hence lower bounds against VSTAT$(t)$ imply lower bounds against STAT$(1/t)$ and upper bounds with STAT$(1/\sqrt t)$ imply upper bounds with VSTAT$(t)$. Moreover, each VSTAT$(t)$ query can be answered from $O(t)$ fresh i.i.d. samples with probability at least $2/3$, and $q$ queries can all be answered correctly with probability $1-\delta$ from $O(t\log(q/\delta))$ samples per query, so a statistical algorithm making $q$ queries to VSTAT$(t)$ is simulated with $O(qt\log(q/\delta))$ samples.

## Proof sketch

Since $p(1-p) \le 1/4$, the VSTAT tolerance $\max\{1/t, \sqrt{p(1-p)/t}\}$ is at most $1/\sqrt{t}$ for $t \ge 1$, and it is at least $1/t$. For the simulation, the empirical mean of $h$ over $m$ samples has variance $p(1-p)/m$, so by Bernstein's inequality it deviates from $p$ by more than $\max\{1/t, \sqrt{p(1-p)/t}\}$ with probability at most a constant when $m = O(t)$, and at most $\delta/q$ when $m = O(t\log(q/\delta))$.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)
- [Hoeffding's inequality for averages of bounded variables](../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Proof depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)
- [Hoeffding's inequality for averages of bounded variables](../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214.
