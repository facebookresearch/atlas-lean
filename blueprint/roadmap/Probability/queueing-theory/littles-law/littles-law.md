# Little's law

Let $0 \le t_1 \le t_2 \le \cdots$ be arrival times with $t_n \to \infty$, and let customer $n$
stay in the system for a sojourn time $W_n \in [0, \infty)$, during $[t_n, t_n + W_n)$. Let
$N(t) = \#\{n : t_n \le t\}$ and $L(s) = \#\{n : t_n \le s < t_n + W_n\}$. Suppose that the
arrival rate and the average sojourn time

$$
\lambda = \lim_{t \to \infty} \frac{N(t)}{t}, \qquad
w = \lim_{n \to \infty} \frac{1}{n} \sum_{j=1}^n W_j
$$

both exist and are finite. Then the time-average number in the system

$$
l = \lim_{t \to \infty} \frac{1}{t} \int_0^t L(s)\,ds
$$

exists and $l = \lambda w$.

The statement is about a single sample path: no stationarity, independence or distributional
assumption is made, and customers may depart in any order.

## Proof depends on

- [Area under the number-in-system path](area-under-number-in-system.md): the area $\int_0^t L$
  lies between the sojourn times of the customers who have left by time $t$ and those of all
  customers who have arrived by time $t$.

## Sources

- K. Sigman, *Notes on Little's Law ($l = \lambda w$)*, lecture notes, Columbia University (2009), <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-LL.pdf>, Section 1.1, Theorem 1.1 and its proof.
