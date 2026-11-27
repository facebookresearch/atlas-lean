# Backward recursion for prospective reserves in a discrete-time Markov model

Let the state space be finite and nonempty and $n \ge 1$. For $k < n$ let $K_k(i, \cdot)$ be a probability distribution on states (transition probabilities, possibly depending on $k$), let $\pi_k(i)$ be premiums, $b_{k+1}(i, j)$ transition benefits, $R_k(i) > 0$ one-period accumulation factors, and $g$ terminal values, with no endowment counted both in $b_n$ and in $g$. For a start state $i$ at date $k$, let the path law be the iterated product of the kernels and define $V_k(i)$ as the expected discounted cash flow: minus premiums paid at the start of each period, plus transition benefits and the terminal value, each discounted by the product of $R^{-1}$ along the path. Then $V_n = g$ and, for $k < n$, $V_k(i) = -\pi_k(i) + R_k(i)^{-1}\sum_j K_k(i, j)(b_{k+1}(i, j) + V_{k+1}(j))$, by conditioning on the first step. Defining $V$ from its start state avoids conditioning on states of probability zero.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
