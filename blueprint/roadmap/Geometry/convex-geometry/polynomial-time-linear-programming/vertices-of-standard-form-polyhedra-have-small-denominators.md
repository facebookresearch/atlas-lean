# Vertices of standard-form polyhedra have small denominators

Let $A$, $b$ be integer data with measure $L$ as in [the encoding size page](encoding-size-of-a-linear-program.md), and let $x$ be a vertex of the polyhedron $\{x \in \mathbb{R}^n : A x = b,\ x \ge 0\}$. Then

$$x = \Bigl(\frac{p_1}{q}, \frac{p_2}{q}, \dots, \frac{p_n}{q}\Bigr)$$

for natural numbers $p_1, \dots, p_n, q$ with $0 \le p_i < 2^L$ and $1 \le q < 2^L$.

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 11.2, Theorem 15 (proof by Cramer's rule on a basis).
