# Scalar Gaussian divergence formula is the one-dimensional vector formula

For all real $m_1, m_2, v_1, v_2$,

$$\frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right) = \frac{1}{2}\left(\log\frac{\det T}{\det S} - n + \operatorname{tr}(T^{-1} S) + (m - q)^{\mathsf T} T^{-1} (m - q)\right),$$

where the right side is the multivariate Gaussian divergence closed form evaluated in dimension $n = 1$ at the mean vectors $m = (m_1)$, $q = (m_2)$ and the $1 \times 1$ covariance matrices $S = (v_1)$, $T = (v_2)$. The parameters are unrestricted, so both sides use the convention $\log x = \log|x|$ with $\log 0 = 0$ (for example when $v_2/v_1 < 0$), the convention $x/0 = 0$, and $(0)^{-1} = (0)$ for the $1 \times 1$ inverse.
