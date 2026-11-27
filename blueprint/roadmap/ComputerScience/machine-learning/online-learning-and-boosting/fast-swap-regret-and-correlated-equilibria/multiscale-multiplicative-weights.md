# Multi-scale multiplicative weights for swap regret

Fix $n \ge 2$ actions and a target $\varepsilon \in (0,1]$, and round the parameters up to integers: the number of levels is $S = \lceil \log_2(1/\varepsilon) \rceil + 1$, the block size is $H = \lceil 4\log(n)\,2^{2S} \rceil = \Theta(\log n/\varepsilon^2)$, and the algorithm runs for the integer horizon $T = H^{2^S}$ days (for $n = 1$ swap regret is identically zero). The **multi-scale multiplicative weights** algorithm maintains $2^S$ threads; thread $k \in [2^S]$ restarts every $H^k$ days, $T/H^k$ times in total, and during each run, which lasts $H^k$ days, it groups $H^{k-1}$ consecutive days into one meta-day and runs multiplicative weights for $H$ meta-day steps on the meta-day aggregated losses. Since $H$ and $2^S$ are integers, all thread counts, run lengths and restart counts are integers. On each day the learner plays the uniform mixture of the current distributions of all threads.

## Depends on

- [Hedge weight update](../hedge-algorithm/update.md)

## Sources

- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647, Algorithm 2.
