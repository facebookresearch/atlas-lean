# Stationarity of the Erlang loss distribution and the Erlang-B recursion

Let $c \ge 0$ be an integer, $\lambda \ge 0$, $\mu > 0$ and $a = \lambda/\mu$. Let $Q$ be the rate matrix on $\{0, \dots, c\}$ with $Q(n, n+1) = \lambda$ for $n < c$ and $Q(n, n-1) = n\mu$ for $n \ge 1$. The Erlang loss distribution $\pi$ (for $c = 0$, the point mass at $0$) is in detailed balance with $Q$, hence $\pi e^{tQ} = \pi$ for every $t \ge 0$; for $\lambda > 0$ the chain is irreducible and $\pi$ is its unique stationary distribution. The full-state mass $B(c, a) = \pi_c$ satisfies $B(0, a) = 1$ and $B(c, a) = aB(c-1, a)/(c + aB(c-1, a))$ for $c \ge 1$; for $a = 0$ this gives $B(c, 0) = 0$ for $c \ge 1$. That $\pi_c$ is also the long-run fraction of arriving customers who are blocked is a further statement that needs Poisson arrivals to see time averages.

## Depends on

- [Erlang's loss formula](erlang-loss-formula.md): the Erlang loss distribution $\pi$.

## Proof depends on

- [Erlang's loss formula](erlang-loss-formula.md): uniqueness of $\pi$ among solutions of the balance relations.
- [Detailed balance implies invariance for the transition semigroup](../../markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/vec-mul-ctmc-transition.md): detailed balance with a rate matrix gives invariance under the transition semigroup.
- [Invariance under the semigroup](../../markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/vec-mul-eq-zero-iff-forall-vec-mul-ctmc.md): a stationary distribution satisfies $\pi Q = 0$, which for this birth–death generator reduces to the balance relations by summing the first $n$ equations, giving uniqueness.

## Background

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): needed for the arrival-seen blocking interpretation, which is not claimed here.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §11.2 (Example 11.2.1, formula (11.2)) and §11.3 (recursion (11.3) with $B(0, \rho) = 1$)
