# Scalar Gaussian KLReal eq multivariate Gaussian KLReal

For all real numbers $m_1, m_2, v_1, v_2$, the scalar Gaussian divergence closed form

$$D(m_1, m_2, v_1, v_2) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right)$$

equals the multivariate closed form in dimension one,

$$\frac{1}{2}\left(\log\frac{\det T}{\det S} - 1 + \operatorname{tr}(T^{-1} S) + (m - q)^{\top} T^{-1} (m - q)\right),$$

evaluated at the vectors $m = (m_1)$, $q = (m_2)$ of the one-dimensional Euclidean space $\mathbb{R}^1$ and the $1 \times 1$ matrices $S = (v_1)$, $T = (v_2)$. No hypothesis on the parameters is needed; both sides use the conventions $x / 0 = 0$, $\log 0 = 0$, and the inverse of a singular matrix is $0$.
