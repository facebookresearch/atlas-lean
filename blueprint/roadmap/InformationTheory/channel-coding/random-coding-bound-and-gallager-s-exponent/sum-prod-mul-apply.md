# Marginal of an independent product

Let $P : X \to \mathbb R$ be real weights on a finite set $X$ with $\sum_x P(x) = 1$ (a law in the
intended use) and $\iota$ a finite index set. For every $i_0 \in \iota$ and every $f : X \to \mathbb R$,

$$\sum_{c : \iota \to X} \Big(\prod_{i} P(c_i)\Big) f(c_{i_0}) = \sum_{x} P(x) f(x).$$

It expands the product of sums $\prod_i \sum_x P(x) h_i(x)$ with $h_{i_0} = f$ and $h_i = 1$
otherwise. This is the step "the average of a product of independent random variables is the product
of the averages" in Gallager's derivation.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Section II, the removal of part 2 of the averaging bar in (8).
