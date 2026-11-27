# Joint PMF apply

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. For every word $w$, the mass of the [product joint distribution](joint-pmf.md) at $w$ is the product of the factor masses, as extended nonnegative reals:

$$
\mathrm{joint}(w) = \prod_{i<n} p_i(w_i).
$$
