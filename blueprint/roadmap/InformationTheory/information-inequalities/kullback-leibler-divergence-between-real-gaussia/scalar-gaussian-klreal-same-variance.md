# The closed-form Gaussian divergence expression at a common variance

Let $m_1, m_2, v \in \mathbb{R}$ with $v \neq 0$. At a common value $v$ of both variance arguments, the closed-form expression

$$D(m_1, m_2, v_1, v_2) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right)$$

reduces to

$$D(m_1, m_2, v, v) = \frac{(m_1 - m_2)^2}{2v}.$$

This is an identity of real expressions: $v$ may be negative, and then for $m_1 \ne m_2$ the value is negative, so it is not the divergence of any pair of Gaussian laws. For a positive variance $v$, the divergence of $\mathcal{N}(m_2, v)$ from $\mathcal{N}(m_1, v)$ is the nonnegative real part $\max(D, 0)$ of this value, see [the divergence between real Gaussians with a common variance](kl-div-gaussian-real-same-variance.md).
