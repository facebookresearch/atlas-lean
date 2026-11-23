# Block index of a list of pairs

The block index of a list
$[(a_1, b_1), \dots, (a_r, b_r)]$ of pairs of natural numbers is the index
$(a_1 + 1, \{1\}^{b_1 - 1}, \dots, a_r + 1, \{1\}^{b_r - 1})$, where $\{1\}^n$ stands for $n$
consecutive entries equal to $1$ and $b_j - 1$ is truncated at $0$.

When all $a_j, b_j \ge 1$ this is an admissible index; it corresponds to the word
$x^{a_1} y^{b_1} \cdots x^{a_r} y^{b_r}$ of the space $\mathfrak{h}^0$ of admissible words in
the letters $x, y$, and the duality $\tau$, the anti-automorphism of
$\mathbb{Q}\langle x, y \rangle$ exchanging $x$ and $y$, maps this word to the word of the block
index of $[(b_r, a_r), \dots, (b_1, a_1)]$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 6 and Theorem 7 (BZ duality), index notation.
