# Staffing an M/M/c queue for a waiting-time target

Consider the first-come first-served M/M/$c$ queue with arrival rate $\lambda > 0$, service rate $\mu > 0$ and offered load $a = \lambda/\mu$, for integers $c > a$, and let $C(c, a)$ be its Erlang-C delay probability. In steady state $E[W] = C(c, a)/(c\mu - \lambda)$ and $P(W > t) = C(c, a)e^{-(c\mu - \lambda)t}$ for $t \ge 0$. Each of the service-level criteria $C(c, a) \le \varepsilon$, $P(W > t) \le \varepsilon$ for a fixed $t \ge 0$, and $E[W] \le w$ is monotone in $c$: if $c$ meets it, so does every larger integer. Consequently, for a finite nonempty set $A$ of allowed integers $c > a$ and a cost $\kappa c$ with $\kappa > 0$, the set of allowed $c$ meeting the criterion is either empty, in which case the staffing problem is infeasible, or consists of all allowed $c$ from its least element $c^*$ on, and $c^*$ is the unique optimal staffing level. If $\lambda = 0$ and $c \ge 1$, the stationary system is empty and the waiting time of a virtual arrival is $0$; no customer-average criterion is defined, since no customers arrive.

Proof. $C(c, a)$ is strictly decreasing in $c$, and so are $e^{-(c\mu - \lambda)t}$ (for $t > 0$; constant for $t = 0$) and $1/(c\mu - \lambda)$, all positive; products of positive nonincreasing functions are nonincreasing. An up-set of a finite set of integers has a least element, and $\kappa c$ is strictly increasing.

## Depends on

- [The Erlang-C delay probability and the mean wait in the M/M/s queue](erlang-c-delay-probability-and-mean-wait.md): the Erlang-C delay probability and the mean wait.

## Proof depends on

- [The Erlang C formula for a real number of servers](erlang-c-for-real-server-numbers.md): the Erlang-C delay probability is strictly decreasing in the number of servers.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Stationary waiting-time tail of the first-come first-served M/M/$c$ queue: $P(W > t) = C(c, a)e^{-(c\mu - \lambda)t}$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §5.3 (distribution of the waiting time in the M/M/$c$ queue)
