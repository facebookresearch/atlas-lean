# Hitting times of closed sets by continuous adapted processes are stopping times

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0})$ be a filtered measurable space, $(E,d)$ a metric space, and $X=(X_t)_{t\ge0}$ an $(\mathcal F_t)$-adapted process with continuous paths in $E$. For a closed set $C\subseteq E$ let

$$\tau_C=\inf\{t\ge0:X_t\in C\}\qquad(\inf\varnothing=+\infty).$$

Then $\tau_C$ is an $(\mathcal F_t)$-stopping time: no completeness or right-continuity of the filtration is needed. Indeed, by continuity of paths and closedness of $C$, for every $t\ge0$

$$\{\tau_C\le t\}=\Bigl\{\inf_{s\in(\mathbb Q\cap[0,t])\cup\{t\}}d(X_s,C)=0\Bigr\},$$

a countable infimum of $\mathcal F_t$-measurable random variables, where $x\mapsto d(x,C)$ is continuous and vanishes exactly on $C$. In particular, for a continuous adapted process with values in $[0,1]$: the absorption time $\inf\{t:X_t\in\{0,1\}\}$; the exit time from the open interval $(a,1-a)$, $0<a<\tfrac12$, which is the hitting time of the closed set $[0,a]\cup[1-a,1]$; and, for processes in a simplex, the hitting times of closed faces and of closed neighbourhoods of them, are stopping times.

## Depends on

- [Filtrations and stopping times](../../../martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)

## Proof depends on

- [The distance to a set is 1-Lipschitz](../../../../Topology/metric-spaces/distance-to-a-set.md)
- [The distance to a nonempty set vanishes exactly on its closure](../../../../Topology/metric-spaces/distance-to-a-set-vanishes-exactly-on-the-closure.md)

## Expansion

A full proof page must establish:

- The displayed identity: if $\tau_C\le t$ the infimum of $s\mapsto d(X_s,C)$ over $[0,t]$ is attained and equals $0$, and by continuity it equals the infimum over the countable dense set; conversely a vanishing infimum over $[0,t]$ is attained at some $s\le t$ with $X_s\in C$.
- The special cases listed above.
- The boundary of the claim: hitting times of open sets are not stopping times for every filtration; they are under right-continuity, as in [usual conditions and continuous-time hitting times](usual-conditions-and-continuous-time-hitting-tim.md).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://doi.org/10.1007/978-1-4612-0949-2>, Ch. 1 (stopping times and hitting times).
