# Quasi-shuffle product

Fix an alphabet and a product of letters $a \diamond b$, a formal
sum of letters given as a finite list (possibly empty, possibly with repetitions). The
quasi-shuffle product $u \ast v$ of two words $u$ and $v$ is the formal sum of words, recorded as
a list, defined recursively by $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty word
$\mathbf{1}$ and by
$a u \ast b v = a (u \ast b v) + b (a u \ast v) + (a \diamond b)(u \ast v)$
for letters $a$, $b$ and words $u$, $v$. Here a letter, or a formal sum of letters, written in
front of a formal sum of words is prepended to each of its words, and the terms are listed in
the order of the formula.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, quasi-shuffle products of Section 2 (the induced quasi-shuffle products on `M`, `𝔎`, `𝔥¹`).
