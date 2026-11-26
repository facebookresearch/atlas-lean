# Factors computed by floating-point Gaussian elimination without pivoting

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. Let $A, L, U$ be $n \times n$ matrices over $K$, with indices $0, \dots, n - 1$. The pair $(L, U)$ is the pair of factors computed from $A$ by Gaussian elimination without pivoting (Doolittle's formulas) in floating point when

- $L$ is unit lower triangular: $L_{ii} = 1$ and $L_{ij} = 0$ for $i < j$;
- $U$ is upper triangular: $U_{ij} = 0$ for $j < i$;
- for $i \le j$, $U_{ij} = \hat s^{(ij)}_i$, and for $i > j$, $L_{ij} = \mathrm{fl}\big(\hat s^{(ij)}_j / U_{jj}\big)$,

where the floating-point value of $A_{ij} - \sum_{k<m} L_{ik} U_{kj}$ is given by the accumulator recurrence

$$\hat s^{(ij)}_0 = A_{ij}, \qquad \hat s^{(ij)}_{k+1} = \mathrm{fl}\big(\hat s^{(ij)}_k - \mathrm{fl}(L_{ik}\, U_{kj})\big):$$

the accumulator starts at $A_{ij}$ without rounding, and each step rounds the product and the subtraction ([subtracting the rounded products one at a time](sub-dot-fl.md)). An empty sum leaves $A_{ij}$ unchanged: the first row of $U$ is $U_{0j} = A_{0j}$, and the first column of $L$ is $L_{i0} = \mathrm{fl}(A_{i0} / U_{00})$, with a single rounding.

These are the operations of Gaussian elimination without pivoting, as in the proof of the backward error analysis of LU decomposition in J. W. Demmel's Math 221 course (UC Berkeley, Lecture 5 notes, 2024), which takes $P = I$; with partial pivoting the same factors are computed for the row-permuted matrix. The relations determine $L$ and $U$ uniquely from $A$, with the convention that a division by $0$ gives $0$; the backward error bounds assume nonzero pivots $U_{jj}$.
