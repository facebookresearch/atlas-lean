# Two-sided geometric mechanism

Let $f : D \to \mathbb{Z}$ and $\varepsilon > 0$, and let $\alpha = e^{-\varepsilon}$. On a database $d$, the two-sided geometric mechanism is the probability mass function on $\mathbb{Z}$ obtained by normalizing $o \mapsto \alpha^{|o - f(d)|}$:

$$
\Pr[o] = \frac{1 - \alpha}{1 + \alpha}\, \alpha^{|o - f(d)|} .
$$

It reports $f(d)$ plus two-sided geometric noise.

## Sources

- A. Ghosh, T. Roughgarden and M. Sundararajan, *Universally Utility-Maximizing Privacy Mechanisms*, STOC 2009 (the two-sided geometric distribution).
