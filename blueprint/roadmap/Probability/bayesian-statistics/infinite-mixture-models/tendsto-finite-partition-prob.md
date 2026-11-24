# The closed-form finite-mixture partition probability tends to the Chinese restaurant process law

For every $\alpha \in \mathbb{R}$, every $n \in \mathbb{N}$ and every partition $\pi$ of $\{1, \dots, n\}$, the [closed-form finite-mixture partition probability](finite-partition-prob.md) $P_K(\pi)$ converges, as $K \to \infty$, to

$$\frac{\alpha^{|\pi|} \prod_{B \in \pi} (|B| - 1)!}{\alpha^{(n)}},$$

the law of the Chinese restaurant process (read as $0$ when the rising factorial $\alpha^{(n)}$ vanishes). This is Griffiths and Ghahramani's Equation 5: the factor $K!/((K - K_+)!\, K^{K_+})$ [tends to $1$](tendsto-desc-factorial-div-pow.md) and each product $\prod_{j=1}^{m-1} (j + \alpha/K)$ [tends to](tendsto-prod-range-add-div.md) $(m - 1)!$. Together with the paper's derivation of the closed form, it identifies the prior on partitions of the infinite mixture model with the Chinese restaurant process.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 2.2, Equation 5.
