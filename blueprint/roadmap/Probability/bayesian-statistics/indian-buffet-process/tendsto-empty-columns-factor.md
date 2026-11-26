# The empty columns contribute $e^{-\alpha H_N}$

For every $\alpha \in \mathbb{R}$ and $N \in \mathbb{N}$,

$$\Big(\frac{N!}{\prod_{j=1}^{N} (j + \alpha/K)}\Big)^K \longrightarrow e^{-\alpha H_N} \quad (K \to \infty),$$

where $H_N = \sum_{j=1}^{N} 1/j$ is the $N$-th harmonic number. In the infinite limit of the finite feature model this is the contribution of the empty columns, whose number $K - K_+$ grows without bound (Griffiths and Ghahramani 2011, Equation 14). The proof writes the factor as $\big(\prod_{j=1}^{N} (1 + (\alpha/j)/K)^K\big)^{-1}$ ([compound interest form](empty-columns-factor-eq.md)) and uses $(1 + t/K)^K \to e^t$.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Equation 14.
