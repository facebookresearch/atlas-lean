# Laplace transform of the absorption time of the neutral Wright–Fisher diffusion

Let $X$ be the neutral Wright–Fisher diffusion without mutation, with generator $\frac{1}{2} x(1 - x) \frac{d^2}{dx^2}$, and let $\tau$ be its [absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) at $\{0, 1\}$, which is [finite almost surely](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md). For $\lambda > 0$ let $u_\lambda(x) = \mathbb{E}_x[e^{-\lambda \tau}]$. Then $u_\lambda$ is the unique function in $C[0, 1] \cap C^2(0, 1)$ with

$$\frac{1}{2} x(1 - x)\, u''(x) = \lambda\, u(x) \quad (0 < x < 1), \qquad u(0) = u(1) = 1,$$

and the family $(u_\lambda)_{\lambda > 0}$ determines the law of $\tau$ under $\mathbb{P}_x$. The law itself has the spectral representation of [the spatial and time integrals of the neutral spectral series](distribution-of-absorption-time-from-the-spectra.md).

## Depends on

- [Absorption time of a frequency path](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md)
- [Absorption in finite time](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md)

## Proof depends on

- [Spatial and time integrals of the neutral spectral series](distribution-of-absorption-time-from-the-spectra.md)
- [Optional stopping theorem in continuous time](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

1. Existence: a solution of the boundary-value problem exists, and by Itô's formula and optional stopping $e^{-\lambda (t \wedge \tau)} u(X_{t \wedge \tau})$ is a bounded martingale, so $u(x) = \mathbb{E}_x[e^{-\lambda \tau}]$.
2. Uniqueness: the difference $w$ of two solutions vanishes at $0$ and $1$ and satisfies $\frac{1}{2} x(1 - x) w'' = \lambda w$, so it has no positive interior maximum and no negative interior minimum.
3. The law of $\tau$ from its Laplace transform, and the agreement with [the spectral representation](distribution-of-absorption-time-from-the-spectra.md).

## Sources

- M. Kimura, Diffusion models in population genetics, *J. Appl. Probab.* 1 (1964), 177–232, <https://doi.org/10.2307/3211856>.
- T. Maruyama, *Stochastic Problems in Population Genetics*, Lecture Notes in Biomathematics 17, Springer (1977), <https://doi.org/10.1007/978-3-642-93065-2>.
