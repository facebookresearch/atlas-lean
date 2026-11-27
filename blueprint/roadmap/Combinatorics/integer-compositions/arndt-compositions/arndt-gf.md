# Generating function of Arndt compositions with parts in a set

An Arndt composition is a
finite sequence $(\sigma_1, \dots, \sigma_k)$ of positive integers such that
$\sigma_{2i-1} > \sigma_{2i}$ for every $i$ with $2i \le k$. For a set $S$ of natural numbers, let
$a_S(n, k)$ be the number of Arndt compositions of $n$ with $k$ parts, all in $S$. The bivariate
generating function of these compositions, by weight ($x$) and number of parts ($y$), is the power
series $A_S(x, y) = \sum_{n \ge 0} \left(\sum_{k=0}^{n} a_S(n, k)\, y^k\right) x^n$ in
$\mathbb{Z}[y][[x]]$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Section 2.
