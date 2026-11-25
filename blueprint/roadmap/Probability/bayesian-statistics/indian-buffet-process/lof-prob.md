# Indian buffet process formula for a lof-class

For $\alpha \in \mathbb{R}$ and a binary matrix $Z$ with $N$ rows and $K_+$ columns, with [feature counts](feature-count.md) $m_k$ and [history counts](history-count.md) $K_h$, the expression

$$\frac{\alpha^{K_+}}{\prod_h K_h!} \cdot e^{-\alpha H_N} \cdot \prod_{k=1}^{K_+} \frac{(N - m_k)!\, (m_k - 1)!}{N!}, \qquad H_N = \sum_{j=1}^{N} \frac1j,$$

with $(m_k - 1)! = 1$ for a zero column. Griffiths and Ghahramani (2011, Equation 14) give it as the probability, under the Indian buffet process with parameter $\alpha$, of the lof-equivalence class whose non-empty columns are those of $Z$. For matrices with non-empty columns it agrees pointwise with the [joint probability of independent Poisson history counts](measure-real-history-count-eq-lof-prob.md); the correspondence between classes and count vectors, and the fact that these values sum to one over classes, are in the source.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Equation 14 and Section 4.5.
