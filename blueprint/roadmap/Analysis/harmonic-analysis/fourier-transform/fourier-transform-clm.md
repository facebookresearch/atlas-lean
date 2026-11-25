# Fourier transform on the Schwartz space

Let $V$ be a finite-dimensional real inner product space with its Lebesgue measure, normalised so that the cube on an
orthonormal basis has measure $1$. Let $\mathbb{k}$ be $\mathbb{R}$ or $\mathbb{C}$, and $E$ a normed space over both
$\mathbb{C}$ and $\mathbb{k}$ whose two scalar multiplications commute. The Fourier transform

$$\mathcal{F}f(w) = \int_V e^{-2\pi i \langle v, w \rangle} f(v) \, dv$$

maps the Schwartz space $\mathcal{S}(V, E)$ to itself, and $\mathcal{F} \colon \mathcal{S}(V, E) \to \mathcal{S}(V, E)$
is a continuous $\mathbb{k}$-linear map. When $E$ is not complete, the integral is $0$ by convention, so
$\mathcal{F}$ is then the zero map. The familiar case is a complex Banach space $E$ with $\mathbb{k} = \mathbb{C}$.
