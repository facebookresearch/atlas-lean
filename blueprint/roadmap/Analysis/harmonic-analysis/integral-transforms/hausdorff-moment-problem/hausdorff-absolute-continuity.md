# Hausdorff's absolute continuity criterion

Let $\mu$ be a probability measure on
$\mathbb{R}^d$ with $\mu(\mathbb{R}^d \setminus I^d) = 0$, where $I^d = [0,1]^d$ is the closed
unit cube, and let $\lambda$ be Lebesgue measure restricted to $I^d$. For a measure $\rho$ write
$m_\rho(n) = \int_{I^d} x^n \, d\rho(x)$ for its moments, indexed by multi-indices
$n \in \mathbb{N}^d$. Then $\mu$ is uniformly absolutely continuous with respect to $\lambda$ if
and only if there is a real constant $C$ such that
$(\Delta^k m_\mu)_n \le C \, (\Delta^k m_\lambda)_n$ for all multi-indices $k \le n$
(coordinatewise), where $\Delta^k$ is the iterated backward difference.

## Sources

- F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*. Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_absolute_continuity`.
