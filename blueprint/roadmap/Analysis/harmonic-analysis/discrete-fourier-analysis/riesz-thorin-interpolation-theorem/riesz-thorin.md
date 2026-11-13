# Riesz–Thorin interpolation theorem on finite sets

Let $\iota$ and $\kappa$ be finite
sets, each with a σ-algebra in which singletons are measurable and with the counting measure, and
write $\|g\|_r \in [0, \infty]$ for the $\ell^r$ norm of $g$ with respect to the counting measure.
Let $p_0, p_1, p, q_0, q_1, q \in [1, \infty]$ and $\theta \in [0, 1]$ satisfy
$1/p = (1-\theta)/p_0 + \theta/p_1$ and $1/q = (1-\theta)/q_0 + \theta/q_1$, where $1/\infty = 0$.
Let $M_0, M_1 \in [0, \infty]$ and let $T : \mathbb{C}^\iota \to \mathbb{C}^\kappa$ be a
$\mathbb{C}$-linear map with $\|Tf\|_{q_0} \le M_0 \|f\|_{p_0}$ and
$\|Tf\|_{q_1} \le M_1 \|f\|_{p_1}$ for all $f \in \mathbb{C}^\iota$. Then
$\|Tf\|_q \le M_0^{1-\theta} M_1^{\theta} \|f\|_p$ for all $f \in \mathbb{C}^\iota$, where
products and powers are computed in $[0, \infty]$ with $0 \cdot \infty = 0$ and $c^0 = 1$.

## Sources

- M. Riesz, Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires, Acta Math. 49 (1927), 465–497, DOI 10.1007/BF02564121; and G. O. Thorin, Convexity theorems generalizing those of M. Riesz and Hadamard with some applications, Comm. Sem. Math. Univ. Lund 9 (1948), 1–58, Riesz-Thorin interpolation theorem; Stein-Shakarchi Complex interpolation; Lean states finite counting-measure complex `→ₗ[ℂ]` form with explicit interpolation identities `p⁻¹=(1-θ)p₀⁻¹+θp₁⁻¹` and bound `M₀^(1-θ)M₁^θ`.
