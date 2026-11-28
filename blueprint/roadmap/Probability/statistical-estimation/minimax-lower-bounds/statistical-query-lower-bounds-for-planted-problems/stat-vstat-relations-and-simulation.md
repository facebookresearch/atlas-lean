# Relations between STAT and VSTAT oracles and their simulation from samples

Let STAT$(\tau)$ answer a query $h : \mathcal{X} \to [0,1]$ with any $v$ satisfying $|v - \mathbb{E}_D[h]| \le \tau$. Then for every $t > 0$ every valid answer of STAT$(1/t)$ is a valid answer of VSTAT$(t)$, and for every $t \ge 1$ every valid answer of VSTAT$(t)$ is a valid answer of STAT$(1/\sqrt{t})$. Hence, for every $t > 0$, lower bounds against STAT$(1/t)$ imply lower bounds against VSTAT$(t)$; and for $t \ge 1$, lower bounds against VSTAT$(t)$ imply lower bounds against STAT$(1/\sqrt{t})$, and upper bounds with STAT$(1/\sqrt t)$ imply upper bounds with VSTAT$(t)$. Moreover, let 1-STAT be the oracle that, given $h : \mathcal{X} \to \{0,1\}$, draws a fresh sample $x \sim D$ and returns $h(x)$. For all integers $t, q > 0$ and every $\delta > 0$ there is an algorithm that, for every input distribution $D$ and every algorithm asking at most $q$ queries to VSTAT, with probability at least $1 - \delta$ gives answers to all of its queries that are valid for VSTAT$(t)$, using $O(qt\log(q/\delta))$ queries to 1-STAT on $D$, that is, $O(t\log(q/\delta))$ fresh samples per query.

## Proof sketch

Since $p(1-p) \le 1/4$, the VSTAT tolerance $\max\{1/t, \sqrt{p(1-p)/t}\}$ is at most $\max\{1/t, 1/(2\sqrt t)\} \le 1/\sqrt{t}$ when $t \ge 1$, and it is at least $1/t$ for every $t > 0$. The restriction $t \ge 1$ is needed: at $t = 1/4$ and $p = 0$ the answer $3$ is within VSTAT's tolerance $4$ but not within STAT's tolerance $2$. For the simulation, a query $h : \mathcal{X} \to [0,1]$ with $p = \mathbb{E}_D[h]$ is turned into Boolean queries $h_\theta(x) = \mathbf{1}[\theta \le h(x)]$ with a fresh uniform $\theta \in [0,1]$ each time, so that each 1-STAT answer is a Bernoulli variable with bias $p$. The mean $v$ of $m$ such answers satisfies $\Pr[|v - p| \ge \sqrt{p(1-p)/t}] \le 2e^{-6m/t}$ by the multiplicative Chernoff bound (for $p \le 1/2$, and symmetrically otherwise), so $m = 6t\ln(2q/\delta)$ answers per query make each answer valid except with probability $\delta/q$, and a union bound over the $q$ queries finishes the proof.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214v6, Definitions 2.3 and 2.4 and Theorem 3.18.
