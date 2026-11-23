# The closed-form finite-model lof-class probability tends to the Indian buffet process formula

For every $\alpha \in \mathbb{R}$ and every binary matrix $Z$ with $N$ rows and $K_+$ columns, the [closed-form finite-model lof-class probability](finite-lof-prob.md) converges, as $K \to \infty$, to

$$\frac{\alpha^{K_+}}{\prod_h K_h!} \cdot e^{-\alpha H_N} \cdot \prod_{k=1}^{K_+} \frac{(N - m_k)!\, (m_k - 1)!}{N!},$$

the [Indian buffet process formula](lof-prob.md) (Equation 14). Of the four factors of the closed form, the label-counting factor $K!/(K_0!\, K^{K_+})$ [tends to $1$](../infinite-mixture-models/tendsto-desc-factorial-div-pow.md), the empty-column factor [contributes $e^{-\alpha H_N}$](tendsto-empty-columns-factor.md), and each non-empty column's product $\prod_{j=1}^{m_k - 1} (j + \alpha/K)$ [tends to](../infinite-mixture-models/tendsto-prod-range-add-div.md) $(m_k - 1)!$. As an identity of formulas it needs no hypothesis on $Z$; the probabilistic reading is for matrices whose columns are all non-empty. Together with the paper's derivation of the closed form, this is how Griffiths and Ghahramani obtain the Indian buffet process from the finite model.

## Background

- [The closed-form finite-mixture partition probability tends to the Chinese restaurant process law](../infinite-mixture-models/tendsto-finite-partition-prob.md): the corresponding limit for class assignments (Griffiths and Ghahramani 2011, Equation 5), on which this derivation is modelled.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Equations 12–14.
