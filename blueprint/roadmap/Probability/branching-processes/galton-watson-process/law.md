# Generation-size law of a Galton–Watson process

For a measure $\nu$ on $\mathbb{N}$ define measures $\mathcal{L}_n$ on $\mathbb{N}$ by
$\mathcal{L}_0 = \delta_1$ and

$$\mathcal{L}_{n+1}(A) = \int \nu^{*k}(A)\, d\mathcal{L}_n(k) ,$$

where $\nu^{*k}$ is the $k$-fold convolution power of $\nu$ (with $\nu^{*0} = \delta_0$). When
$\nu$ is a probability measure, the offspring law, $\mathcal{L}_n$ is the law of the generation
size $Z_n$ of the Galton–Watson process started from one individual: $Z_0 = 1$ and, given
$Z_n = z$, the next generation $Z_{n+1}$ has law $\nu^{*z}$.
