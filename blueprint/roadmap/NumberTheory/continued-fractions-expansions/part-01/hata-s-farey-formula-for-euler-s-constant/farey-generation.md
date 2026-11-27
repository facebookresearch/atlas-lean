# Stern-Brocot generations

The $n$-th Stern-Brocot generation $F_n$ is a finite set of
intervals $[a/b, c/d]$, each stored as the quadruple $(a, b, c, d)$ of natural numbers. It is
defined by $F_0 = \{[0/1, 1/1]\}$, and $F_{n+1}$ is obtained by replacing each
$[a/b, c/d] \in F_n$ with its two mediant halves $[a/b, (a + c)/(b + d)]$ and
$[(a + c)/(b + d), c/d]$.

## Sources

- Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1).
