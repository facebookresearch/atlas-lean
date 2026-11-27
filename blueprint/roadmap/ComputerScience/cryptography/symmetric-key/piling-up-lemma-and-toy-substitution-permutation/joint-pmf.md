# Joint PMF

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. The product joint distribution of $p_0, \dots, p_{n-1}$ is the distribution on $\mathrm{Bool}^n$ with mass

$$
\mathrm{joint}(w) = \prod_{i<n} p_i(w_i),
$$

computed in extended nonnegative reals. These masses sum to one, and the coordinates are independent with marginals $p_i$ by construction. For $n = 0$ it is the point mass at the empty word.
