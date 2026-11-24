# Aalen–Johansen limit law on a fixed grid

For cause-specific hazard increments $x_{i,c}$ at grid times $i = 1, \dots, K$ and causes $c = 1, \dots, r$, the Aalen–Johansen map is $F_c(j) = \sum_{i\le j}S_{i-1}x_{i,c}$ with $S_{i-1} = \prod_{l<i}(1 - \sum_ex_{l,e})$. If estimated increments satisfy $\sqrt n(\hat x_n - x) \Rightarrow G$, then $\sqrt n(F(\hat x_n) - F(x))$ converges in distribution to the derivative of $F$ at $x$ applied to $G$.
