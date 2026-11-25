# Hitting times of open sets under a right-continuous filtration

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0})$ be a filtered measurable space, $(E,d)$ a metric space and $X$ an $(\mathcal F_t)$-adapted process with right-continuous paths in $E$. For an open set $O\subseteq E$ let $\tau_O=\inf\{t\ge0:X_t\in O\}$. Then for every $t\ge0$

$$\{\tau_O<t\}=\bigcup_{s\in\mathbb Q\cap[0,t)}\{X_s\in O\}\in\mathcal F_t,$$

so $\tau_O$ is an optional time; if the filtration is right-continuous, $\mathcal F_t=\bigcap_{u>t}\mathcal F_u$, then $\tau_O$ is a stopping time. In particular this holds under the usual conditions (right-continuous and complete), and for continuous paths.

Right-continuity of the filtration cannot be dropped: for a random sign $\xi\in\{-1,1\}$ with $\mathbb P(\xi=1)\in(0,1)$, the process $X_t=t\xi$ with its natural filtration and $O=(0,\infty)$ has $\{\tau_O=0\}=\{\xi=1\}\notin\mathcal F_0=\{\varnothing,\Omega\}$.

For closed sets and continuous paths no condition on the filtration is needed, by [hitting times of closed sets](hitting-times-of-closed-sets-by-continuous-adapt.md). Hence the absorption time $\inf\{t:X_t\in\{0,1\}\}$ of a continuous adapted $[0,1]$-valued process is a stopping time for every filtration to which the process is adapted.

## Depends on

- [Filtrations and stopping times](../../../martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)
- [Hitting times of closed sets by continuous adapted processes are stopping times](hitting-times-of-closed-sets-by-continuous-adapt.md)

## Expansion

A full proof page must establish:

- The displayed identity, from openness of $O$ and right-continuity of the paths.
- Optional times are stopping times for a right-continuous filtration: $\{\tau\le t\}=\bigcap_n\{\tau<t+1/n\}\in\bigcap_{u>t}\mathcal F_u$.
- The counterexample with $X_t=t\xi$.
- The absorption-time corollary from the closed-set case.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Sec. 1.2 (stopping times and optional times).
