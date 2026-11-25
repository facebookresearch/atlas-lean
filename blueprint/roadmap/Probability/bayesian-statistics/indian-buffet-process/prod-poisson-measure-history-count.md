# Equation 14 as a product of Poisson probabilities

Let $\alpha \ge 0$ and let $Z$ be a binary matrix with $N$ rows whose columns are all non-zero. Then

$$\prod_{h \ne 0} e^{-\lambda_h} \frac{\lambda_h^{K_h}}{K_h!} = \frac{\alpha^{K_+}}{\prod_h K_h!} \cdot e^{-\alpha H_N} \cdot \prod_{k=1}^{K_+} \frac{(N - m_k)!\, (m_k - 1)!}{N!},$$

where the product runs over the $2^N - 1$ non-zero histories, $\lambda_h$ is the [Poisson rate](history-rate.md) of $h$ and $K_h$ the [history count](history-count.md) of $Z$; the right side is the [Indian buffet process formula](lof-prob.md). The product of the factors $e^{-\lambda_h}$ is $e^{-\alpha H_N}$ by Equation 16, and regrouping the columns of $Z$ by history turns $\prod_h \lambda_h^{K_h}$ into $\alpha^{K_+} \prod_k (m_k - 1)!\,(N - m_k)!/N!$.

This is a pointwise identity: the left side is the joint probability mass function of independent Poisson counts evaluated at the history counts of $Z$. Since a lof-class is the same as a collection of histories with multiplicities, it identifies Equation 14 with the law of independent Poisson history counts, so Equation 14 is a probability distribution on classes (Griffiths and Ghahramani 2011, Section 4.5).

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.5.
