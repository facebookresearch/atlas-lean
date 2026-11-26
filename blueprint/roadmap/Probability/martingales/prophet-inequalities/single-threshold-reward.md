# Payoff from the first accepted observation

Let $v_1,\ldots,v_n$ be real observations and let $A\subseteq\mathbb R$ be the set of accepted values. The payoff is $v_i$ for the least index $i$ with $v_i\in A$, or zero if no observation lies in $A$. Equivalently, the payoff is the sum of the $v_i$ over indices satisfying both $v_i\in A$ and $v_j\notin A$ for every $j<i$. There is at most one such index, and the empty sum is zero.

For a threshold $p$, taking $A=[p,\infty)$ accepts a tie and taking $A=(p,\infty)$ rejects it.
