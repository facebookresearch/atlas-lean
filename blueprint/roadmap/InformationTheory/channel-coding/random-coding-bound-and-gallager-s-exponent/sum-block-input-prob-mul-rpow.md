# Letter-by-letter factorisation

For every output word $y = (y_1, \dots, y_N)$ and every $\rho$,

$$\sum_{x} P(x)\, W^N(y \mid x)^{1/(1+\rho)} = \prod_{i=1}^{N} g_{y_i}(\rho),$$

where $P(x) = \prod_i p(x_i)$ and $g_b$ is [Gallager's inner sum](gallager-inner.md): the sum of
products over all words is the product of the letter sums.

## Background

- [Block transition probability](block-transition.md) and
  [probability of a code word](block-input-prob.md): both are products over the letters.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equations (14)–(16).
