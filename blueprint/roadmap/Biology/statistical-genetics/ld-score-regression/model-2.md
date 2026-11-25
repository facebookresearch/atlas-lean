# The LD-score model on the product space

Let $\nu$ be a probability measure on $\mathbb{R}$ satisfying the
[bounded unit law](is-bounded-unit-law.md) condition with bound $C$, let $h^2 \in [0, 1]$, and let
$N$ and $M$ be natural numbers. The model on the product space is the [LD-score model](model.md)
under the [product measure](coord-measure.md) $\nu^{\otimes \mathbb{N}}$ with $N$ individuals
$i = 0, \dots, N - 1$, $M$ markers $k = 0, \dots, M - 1$, heritability $h^2$, effects
$\beta_k(\omega) = \sqrt{h^2 / M}\, \omega_{2k}$ (even coordinates) and noise
$\varepsilon_i(\omega) = \sqrt{1 - h^2}\, \omega_{2i+1}$ (odd coordinates).
