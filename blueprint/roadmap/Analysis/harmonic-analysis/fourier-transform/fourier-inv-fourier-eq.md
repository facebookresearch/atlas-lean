# Fourier inversion formula

Let $V$ be a finite-dimensional real inner product space with its Lebesgue measure, normalised so that the cube on an
orthonormal basis has measure $1$, and $E$ a complex Banach space. For an integrable $f \colon V \to E$ let
$\mathcal{F}f(w) = \int_V e^{-2\pi i \langle v, w \rangle} f(v) \, dv$, and for an integrable $g \colon V \to E$ let
$\mathcal{F}^{-1}g(v) = \int_V e^{2\pi i \langle v, w \rangle} g(w) \, dw$. If $f$ is continuous and integrable and
$\mathcal{F}f$ is integrable, then $\mathcal{F}^{-1}(\mathcal{F}f) = f$.
