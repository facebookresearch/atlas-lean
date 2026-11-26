# Parseval identity for Walsh epistasis coefficients

**Setting.** Consider $L$ biallelic loci and the $2^L$ genotypes $g \in \{0,1\}^L$, listed in the canonical order of ascending $L$-bit binary numbers. A fitness landscape is a vector $\vec W \in \mathbb{R}^{2^L}$ of genotype fitnesses. Let $\Psi$ be the $2^L \times 2^L$ Sylvester–Hadamard matrix, $\Psi_{g,h} = (-1)^{g \cdot h}$, which is symmetric with entries $\pm 1$ and satisfies $\Psi^{\mathsf T}\Psi = 2^L I$. The vector of *epistatic (Walsh) coefficients* of $\vec W$ is

$$\vec E_W = 2^{-L}\, \Psi \vec W, \qquad \text{equivalently} \qquad \vec W = \Psi \vec E_W,$$

where the coefficient indexed by $h$ measures the interaction among the loci in the support of $h$ (order $|h|$).

**Theorem.** For any two landscapes $\vec W, \vec X \in \mathbb{R}^{2^L}$, with $\|\cdot\|^2$ the sum of squares,

$$\|\vec W - \vec X\|^2 = 2^L\, \|\vec E_W - \vec E_X\|^2.$$

## Expansion

Since $\vec W - \vec X = \Psi(\vec E_W - \vec E_X)$, the sum of squares is $(\vec E_W - \vec E_X)^{\mathsf T}\Psi^{\mathsf T}\Psi(\vec E_W - \vec E_X) = 2^L\|\vec E_W - \vec E_X\|^2$. The Walsh transform is a rotation followed by a uniform scaling, so least-squares questions about landscapes can be posed equivalently on epistatic coefficients.

## Sources

- D. M. Weinreich, Y. Lan, J. Jaffe and R. B. Heckendorn, "The Influence of Higher-Order Epistasis on Biological Fitness Landscape Topography", *Journal of Statistical Physics* (2018), Sect. 2.2 (Eq. 1) and Appendix, Theorem 1. <https://doi.org/10.1007/s10955-018-1975-3> (PMC5986866)
