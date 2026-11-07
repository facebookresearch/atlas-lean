# Fourier slice theorem and injectivity of the Radon transform on Schwartz functions

Write $R$ for the Radon transform, $\hat g$ for the one-dimensional Fourier transform of
$g : \mathbb{R} \to \mathbb{C}$ and $\hat f$ for the two-dimensional Fourier transform of
$f : \mathbb{R}^2 \to \mathbb{C}$. For every Schwartz function
$\varphi : \mathbb{R}^2 \to \mathbb{C}$ and all $\theta, k \in \mathbb{R}$, the Fourier transform
of $p \mapsto R\varphi(p, \theta)$ at $k$ equals $\hat\varphi(k\cos\theta, k\sin\theta)$.
Moreover, there is a map $S$ sending functions $\mathbb{R}^2 \to \mathbb{C}$ to functions
$\mathbb{R}^2 \to \mathbb{C}$ such that $S(R\varphi) = \varphi$ for every Schwartz function
$\varphi$.

The second part says only that $R$ is injective on Schwartz functions; no formula, linearity or
continuity is asserted for the left inverse $S$.

## Sources

- J. Radon (1917); R. N. Bracewell (Fourier slice theorem, 1956). Knill, *Some fundamental theorems in mathematics*, §100. Via leanprover/lean-eval@38361be, problem `radon_transform_inversion`.
