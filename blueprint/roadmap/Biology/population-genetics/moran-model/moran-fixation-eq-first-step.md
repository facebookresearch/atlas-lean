# First-step equation of the Moran fixation probability

For every real $r > 0$ and natural numbers $N$ and $i \ge 1$, the [fixation probability](moran-fixation.md) satisfies

$$\varphi_i = a_i\, \varphi_{i+1} + b_i\, \varphi_{i-1} + (1 - a_i - b_i)\, \varphi_i,$$

with the [up-step](moran-up.md) and [down-step](moran-down.md) probabilities $a_i$ and $b_i$. For the interior states $0 < i < N$ this is the first-step equation of the chain; the identity is algebraic, a consequence of $r\, b_i = a_i$, so it holds for every $i \ge 1$.

## Sources

- P. A. P. Moran, *Random processes in genetics*, Proc. Cambridge Philos. Soc. 54 (1958), 60–71.
