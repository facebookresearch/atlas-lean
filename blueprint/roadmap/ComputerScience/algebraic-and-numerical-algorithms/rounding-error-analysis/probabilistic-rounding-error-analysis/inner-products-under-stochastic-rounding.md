# Inner products under stochastic rounding

Let $a, b \in \mathbb{R}^n$ and let $\hat y$ be the value of $y = a^T b$ computed in binary floating-point arithmetic of precision $t$, $u = 2^{-t}$ with $2u < 1$, with [stochastic rounding](stochastic-rounding.md), in any order of summation. Assume that the exponent range is unbounded, or that no intermediate result underflows or overflows, so that every rounding error satisfies $|\delta| \le 2u$. For $\lambda > 0$ let

$$\tilde\gamma_n^{(s)}(\lambda) = \exp\Big(\frac{2\lambda\sqrt n\,u + 4 n u^2}{1 - 2u}\Big) - 1 = 2\lambda\sqrt n\,u + O(u^2).$$

Then

$$\hat y = (a + \Delta a)^T b = a^T (b + \Delta b), \qquad |\Delta a| \le \tilde\gamma_n^{(s)}(\lambda) |a|, \quad |\Delta b| \le \tilde\gamma_n^{(s)}(\lambda) |b|,$$

with probability at least $1 - 2n\exp(-\lambda^2/2)$. No independence assumption is needed. The range assumption is: for the one-term product $\eta \cdot \tfrac12$, with $\eta$ the smallest positive subnormal number of a bounded format, the computed result is $0$ or $\eta$, a relative error of $1$.

## Depends on

- [Stochastic rounding](stochastic-rounding.md)

## Proof depends on

- [Stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md)
- [Probabilistic product bound under mean independence](probabilistic-product-bound-under-mean-independence.md)

## Related topics

- [Probabilistic backward error of inner products](probabilistic-backward-error-of-inner-products.md)

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 4.2, the constant (4.8), the probability $Q(\lambda, n)$ of (4.3), and Theorem 4.9 with its proof. <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
