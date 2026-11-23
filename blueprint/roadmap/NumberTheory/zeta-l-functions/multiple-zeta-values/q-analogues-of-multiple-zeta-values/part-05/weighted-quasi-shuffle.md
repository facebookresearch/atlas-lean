# Weighted quasi-shuffle product

Let $A$ be an alphabet and let $d$ assign to any two
letters $a, b \in A$ a finite formal $\mathbb{Q}$-linear combination
$d(a, b) = \sum_c d(a, b)_c \, c$ of letters. The weighted quasi-shuffle product $u \ast v$ of
two words over $A$ is the finite formal $\mathbb{Q}$-linear combination of words defined by
recursion on total length: $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty word
$\mathbf{1}$, and for letters $a, b$ and words $u, v$,
$a u \ast b v = a (u \ast b v) + b (a u \ast v) + \sum_c d(a, b)_c \, c (u \ast v)$, where
prefixing a letter is extended linearly to combinations of words.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, quasi-shuffle products of Section 2 (with `ℚ`-valued letter product, as for bi-brackets).
