# Klarner's theorem (Erdős Problem 481)

For every $r \in \mathbb{N}$ and all maps
$a, b : \{0, \dots, r - 1\} \to \mathbb{N}$ with $a_i \ge 1$ for every $i$ and
$\sum_{i < r} 1 / a_i > 1$, let $T$ send a finite sequence $(x_1, \dots, x_n)$ of natural numbers
to the sequence of all $a_i x_j + b_i$, listed in blocks for $i = 0, 1, \dots, r - 1$. Then,
starting from $A_1 = (1)$ with $A_{k+1} = T(A_k)$, some $A_k$ has a repeated entry.

This was first shown by Klarner and generalized by Kolpakov and Talambutsa.

## Sources

- T. F. Bloom, Erdős Problems, Problem #481, https://www.erdosproblems.com/481 (status PROVED (LEAN)); resolution: D. A. Klarner, A sufficient condition for certain semigroups to be free, J. Algebra (1982), 140-148; A. Kolpakov and A. Talambutsa, On free semigroups of affine maps on the real line, Proc. Amer. Math. Soc. (2022), 2301-2307, erdosproblems.com/481: true, first shown by Klarner; generalized by Kolpakov and Talambutsa, https://www.erdosproblems.com/481.
