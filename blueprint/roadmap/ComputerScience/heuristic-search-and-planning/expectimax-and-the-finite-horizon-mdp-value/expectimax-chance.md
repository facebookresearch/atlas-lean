# Expectimax Chance

The value of a chance node from its branches $(p_1, t_1), \dots, (p_r, t_r)$: the weighted sum $\sum_i p_i\, v(t_i)$ of the expectimax values $v(t_i)$ of the subtrees, and $0$ for no branches. The weights $p_i$ are arbitrary reals, so the sum need not be an expectation; it is one when the weights are nonnegative and sum to $1$, as in a well-formed chance tree.
