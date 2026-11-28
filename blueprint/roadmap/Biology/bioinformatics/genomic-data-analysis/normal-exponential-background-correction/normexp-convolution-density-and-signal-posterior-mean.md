# Normal–exponential convolution density and signal posterior mean

Let $X = B + S$ where $B \sim \mathcal{N}(\mu, \sigma^2)$ is residual background and $S$ is the true signal, exponentially distributed with mean $\alpha > 0$, independent of $B$. (For a two-colour array, $X = R_f - R_b$ is the foreground minus background intensity of one channel; parameters are separate for each channel of each array.) Write $\varphi$ and $\Phi$ for the standard normal density and distribution function and

$$\mu_{S \cdot X} = x - \mu - \frac{\sigma^2}{\alpha} .$$

**Proposition.**

1. The joint density of $(X, S)$ at $(x, s)$, $s > 0$, is

$$f_{X,S}(x, s) = \frac{1}{\alpha \sigma}\, \exp\!\left(-\frac{x - \mu}{\alpha} + \frac{\sigma^2}{2\alpha^2}\right) \varphi\!\left(\frac{s - \mu_{S \cdot X}}{\sigma}\right).$$

2. The marginal density of $X$ is

$$f_X(x) = \frac{1}{\alpha} \exp\!\left(-\frac{x - \mu}{\alpha} + \frac{\sigma^2}{2\alpha^2}\right) \Phi\!\left(\frac{\mu_{S \cdot X}}{\sigma}\right).$$

3. Given $X = x$, $S$ is $\mathcal{N}(\mu_{S \cdot X}, \sigma^2)$ truncated to $(0, \infty)$, and the background-corrected intensity is

$$\mathbb{E}(S \mid X = x) = \mu_{S \cdot X} + \sigma\, \frac{\varphi(\mu_{S \cdot X}/\sigma)}{\Phi(\mu_{S \cdot X}/\sigma)} > 0 .$$

4. The cumulant generating function of $X$ is $K_X(\theta) = \mu \theta + \tfrac{1}{2}\sigma^2 \theta^2 - \log(1 - \alpha\theta)$ for $\theta < 1/\alpha$.

## Expansion

Multiply the normal density of $B = x - s$ by the exponential density of $S$ and complete the square in $s$: $-\frac{(x - s - \mu)^2}{2\sigma^2} - \frac{s}{\alpha} = -\frac{(s - \mu_{S\cdot X})^2}{2\sigma^2} - \frac{x - \mu}{\alpha} + \frac{\sigma^2}{2\alpha^2}$. Integrating over $s > 0$ gives the factor $\Phi(\mu_{S \cdot X}/\sigma)$; dividing joint by marginal gives the truncated normal, whose mean is the inverse-Mills-ratio formula. Part 4 adds the cumulant generating functions of the normal and the exponential. Because the corrected intensities are strictly positive, log-ratios $M = \log_2(R/G)$ are always defined; adding a small offset $k$ before taking logs, $\log_2[(R + k)/(G + k)]$, further stabilizes their variance at low intensity. Computing $f_X$ naively loses relative accuracy through subtractive cancellation, which is the motivation for careful numerics and for the saddle-point approximation.

## Sources

- J. D. Silver, M. E. Ritchie and G. K. Smyth, "Microarray background correction: maximum likelihood estimation for the normal–exponential convolution", Biostatistics 10 (2009), Section 2.1, Eqs. (2.1)–(2.4), and Section 2.4, <https://doi.org/10.1093/biostatistics/kxn042> (PMC2648902).
