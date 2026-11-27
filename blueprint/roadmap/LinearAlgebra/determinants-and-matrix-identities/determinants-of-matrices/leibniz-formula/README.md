# Leibniz formula for the determinant

Let $R$ be a commutative ring and $M$ a square matrix over $R$ whose rows and columns are indexed by a finite set
$\iota$. Then $\det M = \sum_\sigma \operatorname{sign}(\sigma) \prod_{i \in \iota} M_{\sigma(i), i}$, the sum running over
the permutations $\sigma$ of $\iota$. For an $n \times n$ matrix $B$, with rows and columns indexed by $\{1, \dots, n\}$,
it reads $\det B = \sum_{\sigma \in S_n} \operatorname{sign}(\sigma)\, b_{\sigma(1), 1} \cdots b_{\sigma(n), n}$.

## Idea

The formula expands the determinant into one signed product for each permutation, and each product takes one entry from
every row and every column. So the determinant is a polynomial in the entries, linear in each column and in each row
separately. For a $2 \times 2$ matrix with rows $(a, b)$ and $(c, d)$ it gives $ad - bc$; for $3 \times 3$ matrices it
gives the six-term rule of Sarrus. Replacing $\sigma$ by its inverse, which has the same sign, gives the row form
$\sum_\sigma \operatorname{sign}(\sigma)\, b_{1, \sigma(1)} \cdots b_{n, \sigma(n)}$, so a matrix and its transpose have
the same determinant. Many books take the formula as the definition of the determinant. With its $n!$ terms it is not a
practical way to compute a large determinant: Gaussian elimination needs a number of operations of order $n^3$.

## Statements

- [Leibniz formula for the determinant](det-apply.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 9.46, the case of $n \times n$ matrices with real or complex entries, $n \ge 1$ (version read: the open-access PDF dated 4 November 2026).
