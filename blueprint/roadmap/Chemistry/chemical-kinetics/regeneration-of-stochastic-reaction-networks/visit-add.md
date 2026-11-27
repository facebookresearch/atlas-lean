# Visits after a visit

Let $S$ be a set, $x_0, x \in S$ and $\omega$ a step sequence, and write $V_k(x_0, x, \omega)$ for
the [$k$-th visit](visit.md) to $x_0$, counting from $0$, of the jump chain started at $x$. If
$V_k(x_0, x, \omega) = n$ for a natural number $n$, then for every $j \in \mathbb{N}$

$$V_{k+j}(x_0, x, \omega) = n + V_j(x_0, x_0, \theta_n \omega)$$

in $\mathbb{N} \cup \{\infty\}$, with $n + \infty = \infty$, where $\theta_n \omega$, with
$(\theta_n \omega)_m = \omega_{n+m}$, is the
[shifted step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md):
the $(k+j)$-th visit is $n$ plus the $j$-th visit of the chain restarted at $x_0$ with the shifted
steps, and one is infinite exactly when the other is.
