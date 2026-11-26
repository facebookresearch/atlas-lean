# Efficient Augmentation

For functions $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ (propensity and outcome regressions), the efficient augmentation of the AIPW score is the function

$$h^*(x) = \frac{m_1(x)}{e(x)} + \frac{m_0(x)}{1 - e(x)}, \qquad x \in \mathcal{X},$$

with the convention $a / 0 = 0$.
