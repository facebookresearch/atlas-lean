# Independent Poisson history counts reproduce Equation 14

Let $\alpha \ge 0$, let $(\Omega, \mathbb{P})$ be a measure space, and let $(K'_h)_{h \in \{0,1\}^N}$ be mutually independent measurable random counts such that $K'_h \sim \mathrm{Poisson}(\lambda_h)$ for every non-zero history $h$, with $\lambda_h = \alpha\,(m_h - 1)!\,(N - m_h)!/N!$ the [history rate](history-rate.md) (the construction of Griffiths and Ghahramani 2011, Section 4.5). Then for every binary matrix $Z$ whose columns are all non-zero,

$$\mathbb{P}\big(K'_h = K_h(Z) \text{ for every non-zero } h\big) = \frac{\alpha^{K_+}}{\prod_h K_h!} \cdot e^{-\alpha H_N} \cdot \prod_{k=1}^{K_+} \frac{(N - m_k)!\, (m_k - 1)!}{N!},$$

the [Indian buffet process formula](lof-prob.md) of the lof-class of $Z$ (Equation 14). It follows from the [product identity](prod-poisson-measure-history-count.md) and independence; it is a statement about the count events, one matrix at a time.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.5.
