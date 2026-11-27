# Relations between STAT and VSTAT oracles and their simulation from samples

Let STAT$(\tau)$ answer a query $h : \mathcal{X} \to [0,1]$ with any $v$ satisfying $|v - \mathbb{E}_D[h]| \le \tau$. Then for every $t > 0$ every valid answer of STAT$(1/t)$ is a valid answer of VSTAT$(t)$, and for every $t \ge 1$ every valid answer of VSTAT$(t)$ is a valid answer of STAT$(1/\sqrt{t})$. Hence, for every $t > 0$, lower bounds against STAT$(1/t)$ imply lower bounds against VSTAT$(t)$; and for $t \ge 1$, lower bounds against VSTAT$(t)$ imply lower bounds against STAT$(1/\sqrt{t})$, and upper bounds with STAT$(1/\sqrt t)$ imply upper bounds with VSTAT$(t)$. Moreover, for $t \ge 1$, each VSTAT$(t)$ query can be answered from $O(t)$ fresh i.i.d. samples with probability at least $2/3$, and $q$ queries can all be answered correctly with probability $1-\delta$ from $O(t\log(q/\delta))$ samples per query, so a statistical algorithm making $q$ queries to VSTAT$(t)$ is simulated with $O(qt\log(q/\delta))$ samples.

## Proof sketch

Since $p(1-p) \le 1/4$, the VSTAT tolerance $\max\{1/t, \sqrt{p(1-p)/t}\}$ is at most $\max\{1/t, 1/(2\sqrt t)\} \le 1/\sqrt{t}$ when $t \ge 1$, and it is at least $1/t$ for every $t > 0$. The restriction $t \ge 1$ is needed: at $t = 1/4$ and $p = 0$ the answer $3$ is within VSTAT's tolerance $4$ but not within STAT's tolerance $2$. For the simulation, the empirical mean of $h$ over $m$ samples has variance at most $p(1-p)/m$ (with equality for $\{0,1\}$-valued $h$), since $\mathrm{Var}(h) \le \mathbb{E}[h^2] - p^2 \le p - p^2$ for $h$ with values in $[0,1]$, so by Bernstein's inequality it deviates from $p$ by more than $\max\{1/t, \sqrt{p(1-p)/t}\}$ with probability at most a constant when $m = O(t)$, and at most $\delta/q$ when $m = O(t\log(q/\delta))$.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214, Definition 2.3.
