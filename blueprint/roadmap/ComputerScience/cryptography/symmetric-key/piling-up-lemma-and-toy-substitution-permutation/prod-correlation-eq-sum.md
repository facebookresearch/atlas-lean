# Prod correlation eq sum

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. With the [sign](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-sign.md) map $s(\mathrm{false}) = 1$, $s(\mathrm{true}) = -1$, the product of the [correlations](correlation.md) expands as a sum over all words:

$$
\prod_{i<n} \mathrm{corr}(p_i) = \sum_{w \in \mathrm{Bool}^n} \prod_{i<n} s(w_i) \cdot \mathrm{toReal}\bigl(p_i(w_i)\bigr).
$$

For $n = 0$ both sides are $1$.
