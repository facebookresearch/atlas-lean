# Poisson arrivals see time averages

Let $N$ be a Poisson process of rate $\lambda > 0$ with arrival times $0 < t_1 < t_2 < \cdots$, and let $X$ be a process on the same probability space with values in a metric space $S$, such as $\mathbb{R}^d$, whose paths are right-continuous with left limits. Assume the lack-of-anticipation condition: for every $t > 0$ the future increments $\{N(t+s) - N(t) : s \ge 0\}$ are independent of the joint past $\{(N(u), X(u)) : 0 \le u \le t\}$. Then for every bounded measurable $f : S \to \mathbb{R}$, almost surely

$$
\lim_{n \to \infty} \frac1n \sum_{k=1}^n f(X(t_k-)) = \lim_{t \to \infty} \frac1t \int_0^t f(X(s))\,ds,
$$

in the sense that if either limit exists then so does the other and they are equal. The arrivals see the left limits $X(t_k-)$, the state just before each arrival, and the statement is about them only: the process equal to $1$ exactly at the arrival epochs and $0$ elsewhere satisfies the independence condition and has $X(t_k-) = 0$, in agreement with its time average $0$, but $X(t_k) = 1$ for every $k$, so sampling the state at the arrival epochs themselves (for a process that is not right-continuous) can fail.

## Depends on

- [Poisson process](../point-processes/poisson-processes/is-poisson-process.md): Poisson processes.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Integrals of bounded predictable processes against the compensated Poisson process are martingales, with the strong law along the arrival times needed here.

## Sources

- K. Sigman, *Continuous-time Markov chains*, lecture notes, Columbia University, 2009, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>, §1.15, the lack-of-anticipation condition and Theorem 1.3 (proof omitted there)
