# Entries of the α-Stirling matrix

Let $R$ be a commutative ring and let
$\alpha_0, \alpha_1, \alpha_2, \dots$ be a sequence in $R$ ($\alpha_0$ is never used). The
α-Stirling entries $s_{i,j} \in R$, for $i, j \ge 0$, are defined recursively by
$s_{i,0} = \alpha_1$ for all $i$, $s_{0,j} = 0$ for $j \ge 1$, and
$s_{i+1,j+1} = s_{i,j} + \alpha_{j+2} s_{i,j+1}$ for all $i, j \ge 0$.

These are the entries of the paper's matrix $S_\alpha(n)$ with indices shifted to start at $0$.
Writing $\hat S_{i,j}$ for the entries of $S_\alpha(n)$ in the paper's $1$-based indexing, the
first column is $\alpha_1$, the rest of the first row is $0$, and
$\hat S_{i,j} = \hat S_{i-1,j-1} + \alpha_j \hat S_{i-1,j}$ for $i, j \ge 2$.

## Sources

- A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4, equation (a-1).
