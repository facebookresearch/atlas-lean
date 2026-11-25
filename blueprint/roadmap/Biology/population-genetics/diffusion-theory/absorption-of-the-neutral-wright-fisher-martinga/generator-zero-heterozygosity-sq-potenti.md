# Neutral generator of the squared-heterozygosity potential

Let `u(z) = (2/3) z (1 - z) (1 + z - z²)`. For every real `y`, the neutral
[backward generator](../wright-fisher-diffusion/generator.md) satisfies

`(L_0 u)(y) = y (1 - y) / 2 · u''(y) = -(2y (1 - y))²`.

The potential vanishes at both endpoints, `u(0) = u(1) = 0`, and `u''(y) = -8y (1 - y)`.
