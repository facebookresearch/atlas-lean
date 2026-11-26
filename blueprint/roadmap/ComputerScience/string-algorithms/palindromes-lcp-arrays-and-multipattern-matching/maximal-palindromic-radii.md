# Maximal palindromic radii at all centers

A word $w = w_0 \cdots w_{n-1}$ has $2n + 1$ **centers** $c = 0, \dots, 2n$: an odd center $c$ is the letter at position $(c-1)/2$ and an even center $c$ is the gap before position $c/2$. The factor $w[\lfloor c/2 \rfloor - k,\, \lceil c/2 \rceil + k)$ is the factor of **radius** $k$ about $c$, of length $2k + (c \bmod 2)$. The **maximal palindromic radius** $\mathrm{rad}_w(c)$ is the largest $k$ for which this factor exists and is a palindrome. Every palindromic factor of $w$ is the factor of some radius $k \le \mathrm{rad}_w(c)$ about its center $c$, so a longest palindromic factor is obtained from a center maximizing the length $2\,\mathrm{rad}_w(c) + (c \bmod 2)$.

## Depends on

- [Palindromes](../../../Combinatorics/combinatorics-on-words/morphic-sturmian-words/palindromic-fixed-points-of-morphisms/is-palindrome.md)

## Sources

- A. Apostolico, D. Breslauer and Z. Galil, "Parallel Detection of All Palindromes in a String", Theoretical Computer Science 141(1-2), 1995.
- G. Manacher, "A New Linear-Time On-Line Algorithm for Finding the Smallest Initial Palindrome of a String", Journal of the ACM 22(3), 1975.
