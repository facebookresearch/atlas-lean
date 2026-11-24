# Moments of first-passage and absorption times

Let $X$ be a regular diffusion on $[0, 1]$ with accessible endpoints, absorption time $\tau$ and Green's function $G$, and let $m_n(x) = E_x[\tau^n]$, $m_0 = 1$. The moment recursion for additive path functionals with $g = 1$ gives $m_n = n\,G(m_{n-1})$ and, with $c = \sup_x\int_0^1G(x, y)\,dy$, the bound $m_n \le n!\,c^n$, so every moment is finite when $c < \infty$. By the Green's representation, $m_n$ is the bounded solution of

$$Lm_n = -n\,m_{n-1} \quad \text{on } (0, 1), \qquad m_n(0) = m_n(1) = 0, \qquad n \ge 1,$$

which for $n = 1$ is the equation $L\,E[\tau] = -1$ with zero boundary values of the lecture notes on one-dimensional diffusions (equation (4.8)). For the neutral Wright–Fisher diffusion, $m_1(x) = -2[x\log x + (1 - x)\log(1 - x)]$, the Kimura–Ohta mean absorption time. Moments conditioned on fixation satisfy the same recursion with the fixation-conditioned sojourn density $G(x, y)u(y)/u(x)$ in place of $G$, where $u$ is the fixation probability; they differ from the unconditional moments and must be kept separate from them.

## Depends on

- [Moment recursion for additive path functionals](../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Green's representation for a regular diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/diffusion-generator-integral-green-funct.md)
- [Kimura–Ohta mean absorption time of a neutral allele](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/mean-absorption-time.md)
- [Sojourn density conditioned on fixation](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/conditional-green.md)

## Expansion

1. The moments of $\tau$ as the case $g = 1$ of the moment recursion.
2. The boundary-value problems $Lm_n = -nm_{n-1}$, $m_n(0) = m_n(1) = 0$, and uniqueness of their bounded solutions.
3. The neutral second moment in closed form, and the case of genic selection.
4. Conditional moments given fixation or loss.

## Sources

- *One dimensional diffusions and boundary conditions*, lecture 17 of the course Stochastic methods for physics and biology, University of Helsinki, spring 2012, Section 4.2.
