# Area under the number-in-system path

Let $0 \le t_1 \le t_2 \le \cdots$ be arrival times with $t_n \to \infty$, and let customer $n$
arrive at $t_n$, stay for a sojourn time $W_n \in [0, \infty)$ and depart at $t^d_n = t_n + W_n$
(customers need not depart in the order they arrived). Let $N(t) = \#\{n : t_n \le t\}$ and let
$L(s) = \#\{n : t_n \le s < t^d_n\}$ be the number of customers in the system at time $s$. Then
for every $t \ge 0$

$$
\int_0^t L(s)\,ds = \sum_{n \,:\, t_n \le t} \min(W_n,\, t - t_n),
$$

and consequently

$$
\sum_{n \,:\, t^d_n \le t} W_n \;\le\; \int_0^t L(s)\,ds \;\le\; \sum_{n=1}^{N(t)} W_n .
$$

Proof: exchanging the finite sum and the integral, customer $n$ with $t_n \le t$ contributes
$\int_{t_n}^t \mathbf 1\{W_n > s - t_n\}\,ds = \min(W_n, t - t_n)$. Each term is at most $W_n$,
which gives the upper bound, and equals $W_n$ when $t_n + W_n \le t$, which gives the lower bound
since the remaining terms are nonnegative.

## Sources

- K. Sigman, *Notes on Little's Law ($l = \lambda w$)*, lecture notes, Columbia University (2009), <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-LL.pdf>, equations (7)–(12).
