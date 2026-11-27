# Residue expression of the ℓ-generalized Fibonacci zeta function

Let $\ell$ be a natural
number, let $\alpha$ be a real number, let $R$ be the set of complex roots of
$X^\ell - \sum_{i\lt \ell} X^i$ other than $\alpha$, let
$c(\beta) = (\beta - 1)/(2 + (\ell + 1)(\beta - 2))$ be the Dresden–Du coefficient, and put
$d = c(\alpha)/\alpha$. For a function $\kappa$ from $\mathbb{C}$ to the natural numbers and an
integer $n$, let $k = \sum_{\beta \in R} \kappa(\beta)$ and let $s_0$ be the possible pole
indexed by $(\kappa, n)$. The residue expression indexed by $(\kappa, n)$ is

$$
\rho_{\kappa,n} = d^{-s_0} \binom{-s_0}{k} d^{-k} \cdot
\frac{k!}{\prod_{\beta \in R} \kappa(\beta)!} \cdot
\prod_{\beta \in R} \left(\frac{c(\beta)}{\beta}\right)^{\kappa(\beta)} \cdot
\frac{1}{\log \alpha},
$$

where $\binom{-s_0}{k} = (-s_0)(-s_0 - 1)\cdots(-s_0 - k + 1)/k!$ is the generalized binomial
coefficient, $d^{-s_0}$ and $d^{-k}$ are principal complex powers, and $\log$ is the principal
branch of the complex logarithm.

No condition is imposed on the real number $\alpha$, and every quotient above uses the
convention $z/0 = 0$: thus $c(\beta) = 0$ when $2 + (\ell + 1)(\beta - 2) = 0$, $d = 0$ when
$\alpha = 0$, and the factor $1/\log \alpha$ is $0$ when $\alpha \in \{0, 1\}$, where
$\log 0 = 0$ and $\log 1 = 0$. The powers of $0$ are $0^w = 0$ for $w \ne 0$ and $0^0 = 1$. The
roots $\beta \in R$ are nonzero, since the polynomial has constant term $-1$ for $\ell \ge 1$ (for
$\ell = 0$ it is $1$ and $R$ is empty). In the source,
$\alpha > 1$ is the dominant root of $X^\ell - \sum_{i\lt \ell} X^i$, and none of these
conventions arises.

## Sources

- Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1.
