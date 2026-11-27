# Moments and renewal property of the perfect-integrator interspike intervals

Gerstein and Mandelbrot (1964) model the membrane state between spikes as a diffusion with unit diffusion coefficient (increment variance $2T$ over time $T$) and constant drift, started at distance $z_0 > 0$ from an absorbing threshold and reset to that distance after each spike. Write $\mu$ for the drift velocity toward the threshold. The interspike interval $T$ is the first-passage time to the threshold, whose law on $(0, \infty)$ is the inverse-Gaussian first-passage density of the Gerstein–Mandelbrot interspike-interval law (with drift $c = \mu$). Then the spike train is a renewal process: successive interspike intervals are independent and identically distributed (the source states independence for the model with drift). For $\mu = 0$ the interval is almost surely finite but has infinite mean (the source says it has no population moments of any order); precisely, $E[T^\alpha] < \infty$ exactly for $\alpha < \tfrac12$, so the interval has no finite moment of order $\ge \tfrac12$. For $\mu > 0$ the interval is almost surely finite with mean $E[T] = z_0/\mu$, the mean of the inverse-Gaussian first-passage law of Brownian motion with positive drift to a fixed level (Folks and Chhikara 1978).

## Depends on

- [Gerstein–Mandelbrot interspike-interval law](../inverse-gaussian-interspike-interval-law/measure-first-passage-time-mem-icc.md)
- [Inverse Gaussian first-passage density](../inverse-gaussian-interspike-interval-law/isi-density.md)

## Expansion

1. The model: the random walk of elementary excitatory and inhibitory inputs, its diffusion limit with drift, the absorbing threshold, and the reset that makes the spike train a renewal process (independence of successive intervals from the strong Markov property at each first passage).
2. The moments for $\mu = 0$: the density reduces to the source's equation (6), $z_0 (4\pi)^{-1/2} T^{-3/2} e^{-z_0^2/(4T)}$, which is negligible near $T = 0$ and decays like $T^{-3/2}$ at infinity, so $\int_0^\infty T^\alpha\, T^{-3/2} e^{-z_0^2/(4T)}\, dT$ is finite exactly when $\alpha < \tfrac12$.
3. The mean $z_0/\mu$ for $\mu > 0$, from the inverse-Gaussian law.

## Sources

- G. L. Gerstein and B. Mandelbrot, Random walk models for the spike activity of a single neuron, Biophys. J. 4 (1964), 41–68, equations (6) and (9). <https://doi.org/10.1016/S0006-3495(64)86768-0>
- J. L. Folks and R. S. Chhikara, The inverse Gaussian distribution and its statistical application: a review, J. Roy. Statist. Soc. Ser. B 40 (1978), 263–289.
