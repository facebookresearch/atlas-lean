# Random time-change representation of density-dependent chains

Fix $d\ge1$, a finite set $\Lambda\subset\mathbb Z^d\setminus\{0\}$ of jump directions, bounded continuous rate functions $\beta_l:\mathbb R^d\to[0,\infty)$ for $l\in\Lambda$, and a scale $N\ge1$. Let $(Y_l)_{l\in\Lambda}$ be independent unit-rate [Poisson processes](../../point-processes/poisson-processes/is-poisson-process-count.md), and let $X^N_0$ be a random vector in $N^{-1}\mathbb Z^d$ independent of $(Y_l)_l$. Then the equation

$$X^N_t=X^N_0+\sum_{l\in\Lambda}\frac lN\,Y_l\!\left(N\int_0^t\beta_l(X^N_s)\,ds\right),\qquad t\ge0,$$

has a unique càdlàg solution defined for all $t\ge0$. It is non-explosive: on every bounded time interval it makes finitely many jumps, because the total jump rate is at most $N\sum_l\sup\beta_l<\infty$. The solution is a continuous-time Markov chain on $N^{-1}\mathbb Z^d$ with initial law that of $X^N_0$ and transition rates

$$q(x,\,x+l/N)=N\beta_l(x),\qquad l\in\Lambda,$$

the density-dependent chain with these rates.

Special case: for one direction $\Lambda=\{1\}$ with constant rate $\beta\equiv\lambda>0$, $X^N_t=X^N_0+Y(N\lambda t)/N$, a Poisson process of rate $N\lambda$ with jumps of size $1/N$; for a general $\beta$ the representation is the unit Poisson process run at the chain's own accumulated rate.

## Depends on

- [Exponential interarrivals give a Poisson process](../../point-processes/poisson-processes/is-poisson-process-count.md)

## Proof depends on

- [Path of a continuous-time Markov chain](../finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
- [Non-explosion criteria and Kolmogorov equations on a countable state space](../finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/non-explosion-criteria-and-kolmogorov-equations.md)

## Expansion

A full proof page must establish the following.

- Construction and uniqueness jump by jump: between jumps the internal clocks $\tau_l(t)=N\int_0^t\beta_l(X^N_s)\,ds$ increase linearly, the next jump is the first time some $\tau_l$ reaches the next point of $Y_l$, and the process is defined up to the limit of its jump times.
- Non-explosion from the bounded total rate.
- The Markov property and the rates: the clocks $\tau_l(t)$ are stopping times for the multiparameter filtration of $(Y_l)$, and the strong Markov property of Poisson processes at these times gives exponential holding times of rate $N\sum_l\beta_l(x)$ and jump to $x+l/N$ with probability $\beta_l(x)/\sum_{l'}\beta_{l'}(x)$; identify the law with the minimal chain of the rate matrix $q$.
- The constant-rate special case.

## Sources

- T. G. Kurtz, *Approximation of Population Processes*, CBMS-NSF Regional Conference Series in Applied Mathematics 36, SIAM (1981), <https://books.google.com/books?id=DOl9i1uN6QEC>, time-change representation (statement and proof).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 6, random time changes (statement and proof).
