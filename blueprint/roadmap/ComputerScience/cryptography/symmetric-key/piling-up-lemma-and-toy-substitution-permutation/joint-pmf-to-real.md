# Joint PMF to Real

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. For every word $w$, converting the mass of the [product joint distribution](joint-pmf.md) to a real number gives the product of the real-converted factor masses:

$$
\mathrm{toReal}\bigl(\mathrm{joint}(w)\bigr) = \prod_{i<n} \mathrm{toReal}\bigl(p_i(w_i)\bigr) =: W(w).
$$
