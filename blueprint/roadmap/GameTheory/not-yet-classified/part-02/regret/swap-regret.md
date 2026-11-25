# Swap regret

For mixed plays $p_t$ over $K$ actions and losses $\ell_t$ at rounds $t = 1, \dots, T$, the swap regret is the expected loss $\sum_t \sum_a p_t(a) \ell_t(a)$ minus the minimum, over all maps $\delta : K \to K$, of $\sum_t \sum_a p_t(a) \ell_t(\delta(a))$.
