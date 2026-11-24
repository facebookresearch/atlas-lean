# Inverse-Gaussian interspike intervals of the perfect integrator

Gerstein and Mandelbrot (1964) model the membrane state between spikes as a diffusion with unit diffusion coefficient (increment variance $2T$ over time $T$) and constant drift, started at distance $z_0 > 0$ from an absorbing threshold and reset to that distance after each spike. Write $\mu$ for the drift velocity toward the threshold. The interspike interval is the first-passage time to the threshold, with density

$$I(T) = \frac{z_0}{\sqrt{4\pi}}\, T^{-3/2} \exp\Bigl(-\frac{(z_0 - \mu T)^2}{4T}\Bigr), \qquad T > 0,$$

which is the source's equation (9) with its drift parameter $c = -\mu$ (coordinates with the threshold at the origin), and successive intervals are independent (the source states this for the model with drift). For $\mu = 0$ the density reduces to the source's equation (6), $z_0 (4\pi)^{-1/2} T^{-3/2} e^{-z_0^2/(4T)}$, under which the mean interval is infinite (the source says the interval has no population moments of any order); in fact, since the density decays like $T^{-3/2}$, $E[T^\alpha] < \infty$ exactly for $\alpha < \tfrac12$, so the interval has no finite moment of order $\ge \tfrac12$. For $\mu > 0$ this is an inverse-Gaussian law with mean $z_0/\mu$, the first-passage law of Brownian motion with positive drift to a fixed level.

## Expansion

1. The model: the random walk of elementary excitatory and inhibitory inputs, its diffusion limit with drift, the absorbing threshold, and the reset that makes the spike train a renewal process.
2. The first-passage density as the diffusion current at the absorber, for the forward equation with an absorbing boundary (equations (6) and (9) of the source).
3. The mean $z_0/\mu$ for $\mu > 0$, from the inverse-Gaussian law.
4. For drift away from the threshold ($\mu < 0$), the total mass $e^{\mu z_0} < 1$ of the density, which is the probability that the threshold is ever reached (derived from the scale density $e^{\mu z}$ of the diffusion with generator $\partial_z^2 - \mu \partial_z$ written in the distance $z$ to the threshold, which vanishes at infinity when $\mu < 0$), as a separate statement.

## Sources

- G. L. Gerstein and B. Mandelbrot, Random walk models for the spike activity of a single neuron, Biophys. J. 4 (1964), 41–68, equations (6) and (9). <https://doi.org/10.1016/S0006-3495(64)86768-0>
- Inverse Gaussian distribution, Wikipedia, section on the relationship with Brownian motion. <https://en.wikipedia.org/wiki/Inverse_Gaussian_distribution>
