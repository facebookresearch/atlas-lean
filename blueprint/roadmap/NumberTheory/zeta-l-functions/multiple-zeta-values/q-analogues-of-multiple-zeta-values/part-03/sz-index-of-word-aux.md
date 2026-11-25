# Reading an index off a word in $p$ and $y$

For $c \in \mathbb{N}$ and a word $w$ in the
letters $p$ and $y$, the index $R_c(w)$, a finite sequence of natural numbers, is defined
recursively by $R_c(\mathbf{1}) = ()$ for the empty word $\mathbf{1}$, $R_c(p w) = R_{c+1}(w)$,
and $R_c(y w) = (c, R_0(w))$, the index with first entry $c$ followed by the entries of
$R_0(w)$. Thus $R_c(p^{k_1} y\, p^{k_2} y \cdots p^{k_r} y\, p^j) = (c + k_1, k_2, \dots, k_r)$
for $r \ge 1$ and $R_c(p^j) = ()$: the entries are the lengths of the blocks of $p$s before
each $y$, with $c$ added to the first, and trailing $p$s are dropped.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, identification of SZ-admissible indices with words of `𝔎¹`.
