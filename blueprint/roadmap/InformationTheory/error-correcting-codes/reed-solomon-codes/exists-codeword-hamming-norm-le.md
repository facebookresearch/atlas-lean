# A low-weight Reed-Solomon codeword

Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1}
\in F$ (not necessarily distinct) and let $1 \le k \le n$. There is a nonzero polynomial
$p \in F[X]$ of degree less than $k$ whose encoding $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ has at
most $n - k + 1$ nonzero coordinates.

One such polynomial is $\prod_{j < k - 1} (X - \alpha_j)$.
