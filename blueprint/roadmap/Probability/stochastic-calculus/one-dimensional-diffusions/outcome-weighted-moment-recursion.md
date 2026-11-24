# Moments of path functionals on the event of fixation

With $X$, $T^*$, $G$ and $A = \int_0^{T^*}g(X_s)\,ds$ as in the moment recursion for additive path functionals, let $u(p) = P_p(X_{T^*} = 1) = (S(p) - S(0))/(S(1) - S(0))$, with $S$ the scale function, and $H_n(p) = E_p[A^n;\ X_{T^*} = 1]$. Then $H_0 = u$ and

$$H_n = n\,G(g\,H_{n-1}), \qquad n \ge 1,$$

by the same decomposition of $A^n$ and the Markov property at time $t$, since the event of fixation is determined by the path after $t$ (derivation). Where $u(p) > 0$, the moments conditional on fixation are $E_p[A^n \mid X_{T^*} = 1] = H_n(p)/u(p)$. The recursion is the case $c = 0$, $d = 1$ of the path functionals between prescribed frequencies, with exit at $d$. The process conditioned on its exit point is again a diffusion; for exit at $0$ this is the conditioned drift of the retrospective sampling model, and the same computation (Etheridge, lecture notes, Example 5.5) with the exit probability $u$ at $1$ in place of $1 - u$ gives drift $\mu + \sigma^2S'(x)/(S(x) - S(0))$ (derivation: $\sigma^2u'/u$ with $u' = S'/(S(1) - S(0))$); $H_n/u$ are the unconditioned moments of $A$ for this conditioned diffusion. Nagylaki (1974, abstract) treats moments of path integrals for conditioned as well as unconditioned processes.

## Depends on

- [Moment recursion for additive path functionals](../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)
- [Path functionals between prescribed frequencies](../../../Probability/stochastic-calculus/one-dimensional-diffusions/functionals-between-prescribed-frequencies.md)
- [A retrospective sampling model for allele age](../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/retrospective-sampling-model.md)
- [Sojourn density conditioned on fixation](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/conditional-green.md)
- [Neutral conditional mean time to fixation](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/neutral-fixation-time.md)

## Expansion

1. The decomposition of $A^n$ on the event of fixation and the Markov property at time $t$.
2. The recursion with $H_0 = u$ and bounds as in the unconditioned case.
3. The diffusion conditioned to exit at $1$, its drift $\mu + \sigma^2S'/(S - S(0))$, and the identification of $H_n/u$ with its moments.
4. The conditional mean fixation time ($g = 1$, $n = 1$) and its agreement with the neutral conditional mean time to fixation.

## Sources

- A. Etheridge, Diffusion process models in mathematical genetics, lecture notes, University of Oxford, Theorem 4.4 and Example 5.5.
- T. Nagylaki, The moments of stochastic integrals and the distribution of sojourn times, Proc. Natl. Acad. Sci. USA 71 (1974), 746–749, abstract. <https://doi.org/10.1073/pnas.71.3.746>
