# A rational number that is a square at every place is a square

Let $r \in \mathbb{Q}$. If
$r$ is a square in $\mathbb{R}$ and in $\mathbb{Q}_p$ for every prime $p$, then $r$ is a square in
$\mathbb{Q}$.

Being a square in $\mathbb{R}$, $r \geq 0$. For $r \neq 0$, being a square in $\mathbb{Q}_p$, $r$
has even $p$-adic valuation $v_p(r)$, so Mathlib's `Rat.isSquare_iff_even_factorization`
applies; $r = 0$ is a square.

## Sources

- A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture notes, Lecture 11, proof of Theorem 11.12, case $n = 2$, p. 4.
