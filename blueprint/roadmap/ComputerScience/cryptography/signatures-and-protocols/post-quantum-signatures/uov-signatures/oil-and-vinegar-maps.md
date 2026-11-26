# Oil-and-vinegar quadratic maps and the UOV trapdoor

Let $\mathbb{F}$ be a finite field and $n = v + o$ with $v$ *vinegar* and $o$ *oil* variables. A homogeneous *oil-and-vinegar* quadratic polynomial in $x = (x_V, x_O)$ is one with no oil–oil monomials, $f(x) = \sum_{i, j \le v} \alpha_{ij} x_i x_j + \sum_{i \le v < j} \beta_{ij} x_i x_j$. The UOV *central map* is $\mathcal{F} = (f_1, \dots, f_o)$ with independent such polynomials, and the *public map* is $\mathcal{P} = \mathcal{F} \circ T$ for a uniform invertible linear map $T$ of $\mathbb{F}^n$. Every polynomial of $\mathcal{F}$ vanishes on the oil subspace $\{x_V = 0\}$, so $\mathcal{P}$ vanishes on the secret subspace $\mathcal{O} = T^{-1}(\{x_V = 0\})$ of dimension $o$. In UOV version 3.0 the oil subspace is the column space of $\binom{\mathbf{O}}{I_o}$ for $\mathbf{O} \in \mathbb{F}^{v \times o}$, each public polynomial is given by an upper-triangular block matrix $\begin{pmatrix} P^{(1)} & P^{(2)} \\ 0 & P^{(3)} \end{pmatrix}$, and $P^{(3)}$ is the unique upper-triangular matrix making $p_i$ vanish on $\mathcal{O}$. The fields are $\mathbb{F}_{16} = \mathbb{F}_2[X]/(X^4 + X + 1)$ and $\mathbb{F}_{256} = \mathbb{F}_2[X]/(X^8 + X^4 + X^3 + X + 1)$.

## Sources

- Ward Beullens et al., "UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation", Version 3.0, 2026.
