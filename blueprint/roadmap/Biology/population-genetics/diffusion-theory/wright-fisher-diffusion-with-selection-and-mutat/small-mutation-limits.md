# Small-mutation limits of stationary laws

For the Wright–Fisher diffusion with genic selection $\sigma$ and mutation rates $\theta_1 = \varepsilon\alpha_1$, $\theta_2 = \varepsilon\alpha_2$ with $\alpha_1, \alpha_2 > 0$ fixed, the stationary law $\pi_\varepsilon(x) \propto x^{\varepsilon\alpha_1 - 1}(1 - x)^{\varepsilon\alpha_2 - 1}e^{2\sigma x}$ converges weakly as $\varepsilon \to 0$ to

$$p_0\,\delta_0 + p_1\,\delta_1, \qquad \frac{p_1}{p_0} = \frac{\alpha_1}{\alpha_2}e^{2\sigma},$$

which is the stationary law of the two-state chain of monomorphic populations in which type $0$ is replaced by type $1$ at rate $\frac{\theta_1}{2}K(\sigma)$ and type $1$ by type $0$ at rate $\frac{\theta_2}{2}K(-\sigma)$, with $K(\sigma) = 2\sigma/(1 - e^{-2\sigma})$ for $\sigma \ne 0$ and $K(0) = 1$ the slope of Kimura's fixation probability at $0$.

Derivation. Near $0$, $\int_0^{1/2}x^{\varepsilon\alpha_1 - 1}(1 - x)^{\varepsilon\alpha_2 - 1}e^{2\sigma x}\,dx = \frac{1}{\varepsilon\alpha_1} + O(1)$, and near $1$ the corresponding integral is $\frac{e^{2\sigma}}{\varepsilon\alpha_2} + O(1)$, while the mass of $[\delta, 1 - \delta]$ stays bounded; dividing by the total mass gives the weak limit and $p_1/p_0 = (\alpha_1/\alpha_2)e^{2\sigma}$. In the chain, the stationary ratio is the ratio of the rates, $\frac{\alpha_1K(\sigma)}{\alpha_2K(-\sigma)} = \frac{\alpha_1}{\alpha_2}\cdot\frac{e^{2\sigma} - 1}{1 - e^{-2\sigma}} = \frac{\alpha_1}{\alpha_2}e^{2\sigma}$ for $\sigma \ne 0$, and $\alpha_1/\alpha_2$ for $\sigma = 0$. The rates are those of new mutants arising in a monomorphic population, each fixing with probability $K(\pm\sigma)$ times its initial frequency, the picture of at most one segregating mutation at a time. Burden and Griffiths (2019) obtain the stationary distribution of a sample from a Wright–Fisher diffusion with general small mutation rates to first order in the rates by a coalescent argument equivalent to at most one mutation in the coalescent tree, and relate it to boundary processes in which mutation moves a monomorphic population to a two-type configuration and no further mutation occurs until fixation.

## Depends on

- [Slope constant of Kimura's fixation probability](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-slope.md)
- [Speed density with selection and mutation](../../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md)

## Expansion

1. The asymptotic masses of the stationary density near $0$ and $1$ as $\varepsilon \to 0$.
2. The weak limit and its weights.
3. The two-state substitution chain and its stationary law.
4. Equality of the two, and the first-order corrections in $\varepsilon$ for samples.

## Sources

- C. J. Burden and R. C. Griffiths, The stationary distribution of a sample from the Wright–Fisher diffusion model with general small mutation rates, J. Math. Biol. 78 (2019), 1211–1224, abstract and Section 1. <https://doi.org/10.1007/s00285-018-1306-y>
