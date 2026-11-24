# Entries of the α-upper matrix

Let $R$ be a commutative ring and let
$\alpha_0, \alpha_1, \alpha_2, \dots$ be a sequence in $R$ ($\alpha_0$ is never used). The
α-upper entries $u_{i,j} \in R$, for $i, j \ge 0$, are defined recursively by $u_{0,j} = 1$ for
all $j$, $u_{i,0} = 0$ for $i \ge 1$, and
$u_{i+1,j+1} = u_{i+1,j} + \alpha_{i+1} u_{i,j} + (\alpha_{j+2} - \alpha_{i+1}) u_{i,j+1}$ for
all $i, j \ge 0$.

These are the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ with indices shifted to start
at $0$; in the paper's $1$-based indexing the first row is $1$, the rest of the first column is
$0$, and $\mathsf{U}_{i,j} = \mathsf{U}_{i,j-1} + \alpha_{i-1} \mathsf{U}_{i-1,j-1} +
(\alpha_j - \alpha_{i-1}) \mathsf{U}_{i-1,j}$ for $i, j \ge 2$.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2, equation (u-1-2).
