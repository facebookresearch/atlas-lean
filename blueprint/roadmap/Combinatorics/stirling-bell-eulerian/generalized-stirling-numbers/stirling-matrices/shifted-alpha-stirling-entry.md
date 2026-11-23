# Entries of the shifted α-Stirling matrix

Let $R$ be a commutative ring and let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$. The entries $\mathsf{S}_{i,j} \in R$ of the
shifted $\alpha$-Stirling matrix of $\alpha$, for natural numbers $i$ and $j$ counted from $0$, are
defined by $\mathsf{S}_{i,0} = \alpha_1$ for all $i$, $\mathsf{S}_{0,j} = \alpha_1$ for all $j$,
and

$$\mathsf{S}_{i+1,j+1} = \mathsf{S}_{i+1,j} + \alpha_{j+2} \mathsf{S}_{i,j+1}.$$

The paper indexes from $1$: its entry $(i, j)$ is $P_{i,j} = \mathsf{S}_{i-1,j-1}$ for
$i, j \ge 1$. In this indexing the first row and the first column equal $\alpha_1$, and
$P_{i,j} = P_{i,j-1} + \alpha_j P_{i-1,j}$ for $i, j \ge 2$.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4.
