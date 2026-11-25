# Trudi's formula for Toeplitz–Hessenberg determinants

Let $R$ be a commutative ring, let $n \ge 1$, and let $a_0, a_1, a_2, \dots \in R$ with $a_0 \ne 0$. Let $A_n$ be the $n \times n$ matrix with entry $a_{i+1-j}$ in row $i$ and column $j$ when $j \le i + 1$, and $0$ otherwise. Then

$$\det A_n = \sum_c (-a_0)^{n - \ell(c)}\, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$

where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, the finite sequences of positive integers with sum $n$.

## Idea

A Toeplitz–Hessenberg matrix is constant along diagonals and vanishes above the first superdiagonal, which carries the constant $a_0$. Expanding the determinant along the first column gives the recurrence $\det A_n = \sum_{k=1}^{n} (-a_0)^{k-1} a_k \det A_{n-k}$, with $\det A_0 = 1$, and unrolling it produces one term for each composition of $n$. Grouping compositions with the same multiset of parts gives Trudi's formula with multinomial coefficients; for $a_0 = 1$ it is Brioschi's formula. By the recurrence, up to signs and powers of $a_0$, these determinants are the coefficients of the inverse of a power series, which turns generating-function identities into determinant identities, as for the Catalan and Fuss–Catalan numbers.

## Statements

- [Trudi's formula for Toeplitz–Hessenberg determinants](det-toeplitz-hessenberg-eq-sum-compositi-2.md)
- [Trudi's formula for Toeplitz–Hessenberg determinants, general case](det-toeplitz-hessenberg-eq-sum-compositi.md): the general case, without $a_0 \ne 0$
- [Toeplitz–Hessenberg determinant](toeplitz-hessenberg-det.md): the Toeplitz–Hessenberg determinant
- [Trudi's formula in composition form](toeplitz-hessenberg-det-eq-sum-compositi.md): the composition form
- [Brioschi's formula: the case $a_0 = 1$ of Trudi's formula](toeplitz-hessenberg-det-eq-neg-one-pow-m.md): special case $a_0 = 1$: Brioschi's formula
- [Trudi's formula when $a_0 = -1$](toeplitz-hessenberg-det-eq-trudi-partiti.md): special case $a_0 = -1$
- [The $1 \times 1$ Toeplitz–Hessenberg determinant](toeplitz-hessenberg-det-one.md): size $1$
- [The $2 \times 2$ Toeplitz–Hessenberg determinant](toeplitz-hessenberg-det-two.md): size $2$
- [Trudi's partition sum](trudi-partition-sum.md): Trudi's partition sum
- [Trudi's partition sum as a sum over compositions](trudi-partition-sum-eq-sum-compositions.md): the partition sum as a sum over compositions
- [Two values of Trudi's partition sum](trudi-partition-sum-examples.md): two values of the partition sum
