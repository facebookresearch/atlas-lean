# Closed-form expression for the divergence between real Gaussians

For real numbers $m_1, m_2, v_1, v_2$, the scalar Gaussian divergence closed form (in nats) is

$$D(m_1, m_2, v_1, v_2) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right)$$

It is defined for all real inputs, with the conventions $x / 0 = 0$, $\log 0 = 0$ and $\log x = \log \lvert x \rvert$ for $x < 0$.
