# First time from $n$ on that the Snell envelope meets the reward

For a reward sequence $(G_k)$ with [Snell envelope](snell-envelope.md) $S$ of horizon $N$ and for
$n \le N$, the first meeting time from $n$ on is
$\tau_n(\omega) = \min\{k \in [n, N] : S_k(\omega) = G_k(\omega)\}$, which exists since
$S_N = G_N$; for $n > N$, when the window $[n, N]$ is empty, it is taken to be $\tau_n = N$. For $n = 0$
it is the [first meeting time](snell-stopping-time.md) $\tau^*$.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, equation (1.1.8).
