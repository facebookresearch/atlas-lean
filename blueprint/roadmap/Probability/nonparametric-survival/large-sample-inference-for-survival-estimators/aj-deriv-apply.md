# Coordinates of the Aalen–Johansen derivative

For cause-specific hazard increments $x_{i,c}$ at grid times $i = 1, \dots, K$ and causes $c = 1, \dots, r$, the Aalen–Johansen map is $F_c(j) = \sum_{i\le j}S_{i-1}x_{i,c}$ with $S_{i-1} = \prod_{l<i}(1 - \sum_ex_{l,e})$. The derivative at $x$ in direction $h$ has coordinates $\sum_{i\le j}\big(S_{i-1}h_{i,c} - x_{i,c}\sum_{m<i}\prod_{l<i,l\ne m}(1 - \sum_ex_{l,e})\sum_eh_{m,e}\big)$.
