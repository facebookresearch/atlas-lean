# The deviatoric return is firmly nonexpansive with the 2μ scaling

Let $\mu$ be real and let $\mathcal K$ be a nonempty convex set of real $3 \times 3$ matrices that
is complete for the Frobenius distance (equivalently, closed). For all real $3 \times 3$ matrices
$\sigma_1$ and $\sigma_2$, not necessarily symmetric, let $s_k$ be the
[deviator](../cauchy-stress-small-strain-and-mohr-s-circle/deviatoric-stress.md) of $\sigma_k$,
$p_k = P_{\mathcal K}(s_k)$ its
[nearest-point projection](../../../Analysis/hilbert-spaces/hilbert-projection-theorem/convex-projection.md)
onto $\mathcal K$ and $\Delta\varepsilon_k = (2\mu)^{-1} (s_k - p_k)$ the
[plastic strain increment](plastic-strain-increment.md), $k = 1, 2$. Then

$$
\|p_1 - p_2\|^2 + (2\mu)^2\, \|\Delta\varepsilon_1 - \Delta\varepsilon_2\|^2
\le \|s_1 - s_2\|^2,
$$

with the [Frobenius norm](frobenius-inner-eq-sum-mul.md) $\|A\|^2 = \sum_{i,j} A_{ij}^2$. The set
$\mathcal K$ need not consist of deviatoric stresses. In the model $\mu > 0$, and the inequality is
the firm nonexpansiveness of the projection; it holds for every real $\mu$, and for $\mu = 0$, where
the increments are $0$ by the convention $0^{-1} = 0$, it reduces to
$\|p_1 - p_2\| \le \|s_1 - s_2\|$.
