# Patterson's normalized genotype matrix

For a real $N \times M$ genotype matrix $C$, Patterson's normalized matrix has entries

$$\frac{C_{ij} - \mu_j}{\sqrt{\hat p_j (1 - \hat p_j)}},$$

where $\mu_j$ is the column mean and $\hat p_j = \mu_j / 2$ the [allele-frequency estimate](allele-freq.md), with the conventions $\sqrt{x} = 0$ for $x < 0$ and $x/0 = 0$. A monomorphic marker ($\hat p_j \in \{0, 1\}$) thus gives a zero column.
