# Swap regret

For play weights $p_t(a)$ (not required to be nonnegative or to sum to $1$) and losses $\ell_t(a)$ over a finite nonempty set of $K$ actions at rounds $t = 1, \dots, T$, the swap regret is the weighted loss $\sum_t \sum_a p_t(a) \ell_t(a)$ minus the minimum, over all maps $\delta : K \to K$, of $\sum_t \sum_a p_t(a) \ell_t(\delta(a))$. When each $p_t$ is a probability distribution on the actions, the first term is the expected loss of the mixed plays.
