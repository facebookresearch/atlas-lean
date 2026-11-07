# Subword shift sets are well based

Let $l$ be a natural number and $\omega$ a binary word
of length $l$, read as a natural number $\omega < 2^l$. Then the set $Q$ of those
$j \in \{1, \dots, l-1\}$ for which the leftmost $l - j$ bits of $\omega$ differ from its
rightmost $l - j$ bits, that is $\lfloor \omega / 2^j \rfloor \ne \omega \bmod 2^{l-j}$, is well
based.

This is the well-based part of Theorem 22 of the paper. Its further claim, that no integer
linear combination of the elements $p_i$ of $\{1, \dots, q\} \setminus Q$ lies in $Q$ (with $q$
the largest element of $Q$), is omitted: for $\omega = 010100101$ and $l = 9$ one gets
$Q = \{1, 2, 3, 4, 6, 8\}$, $q = 8$, $p_1 = 5$, $p_2 = 7$, and $p_2 - p_1 = 2 \in Q$. The side
condition $q = l - 1$ of Theorem 21 is not needed.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Theorem 22.
