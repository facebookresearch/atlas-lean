# Optimal staffing for a loss system over finitely many server counts

Let $\lambda \ge 0$, $\mu > 0$, $a = \lambda/\mu$, weights $\kappa, \beta \ge 0$ and a finite nonempty set $C \subseteq \{0, 1, 2, \dots\}$ of allowed server counts. With $B(c, a)$ the Erlang-B value of the Erlang loss distribution, the cost $F(c) = \kappa c + \beta\lambda B(c, a)$ attains its minimum on $C$, and the values $B(c, a)$, $c \le \max C$, are computed by the recursion $B(0, a) = 1$, $B(c, a) = aB(c-1, a)/(c + aB(c-1, a))$. Reading $\lambda B(c, a)$ as the long-run rate of lost customers in the M/M/c/c system uses the stationarity of the loss distribution and PASTA; neither is used for the minimization itself.

## Depends on

- [Stationarity of the Erlang loss distribution and the Erlang-B recursion](stationary-law-of-the-erlang-loss-system.md): the Erlang-B value $B(c, a)$ and its recursion.

## Background

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): for the lost-customer interpretation only.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §11.2 (formula (11.2)) and §11.3 (recursion (11.3))
