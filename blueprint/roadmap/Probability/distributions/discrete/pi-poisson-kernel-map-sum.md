# Pi Poisson Kernel map sum

Let $\iota$ be a finite index set and let $\kappa$ be the product Poisson kernel from $[0, \infty)^\iota$ to $\mathbb{N}^\iota$, $\kappa(r) = \bigotimes_{i \in \iota} \mathrm{Po}(r_i)$, where $\mathrm{Po}(r)(\{n\}) = e^{-r} r^n / n!$. Pushing $\kappa$ forward along the total count $N \mapsto \sum_i N_i$ gives the Poisson kernel evaluated at the summed mean: for every $r \in [0, \infty)^\iota$,

$$\kappa(r) \circ \Big(N \mapsto \sum_{i \in \iota} N_i\Big)^{-1} = \mathrm{Po}\Big(\sum_{i \in \iota} r_i\Big).$$
