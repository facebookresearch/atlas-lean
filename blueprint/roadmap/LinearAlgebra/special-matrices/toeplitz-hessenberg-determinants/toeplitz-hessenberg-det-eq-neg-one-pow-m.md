# Brioschi's formula: the case $a_0 = 1$ of Trudi's formula

Let $R$ be a commutative ring
and let $a_0, a_1, a_2, \dots$ be elements of $R$ with $a_0 = 1$. For every $n \ge 0$, the
Toeplitz–Hessenberg determinant $\det A_n$ of size $n$ built from $a$ satisfies

$$\det A_n = (-1)^n \sum_\alpha (-1)^{|\alpha|} m_n(\alpha) a_1^{\alpha_1} \cdots a_n^{\alpha_n},$$

where the sum, Trudi's partition sum with weight $-1$ per part, runs over the tuples
$\alpha = (\alpha_1, \dots, \alpha_n)$ of nonnegative integers with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, with $|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 with `a_0 = 1` (the sign `D_+`).
