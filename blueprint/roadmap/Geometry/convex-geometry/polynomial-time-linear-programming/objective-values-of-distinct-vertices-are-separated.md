# Objective values of distinct vertices are separated

Let $A$, $b$, $c$ be integer data with measure $L$ as in [the encoding size page](encoding-size-of-a-linear-program.md), and let $x_1$, $x_2$ be vertices of $\{x : A x = b,\ x \ge 0\}$. If $c^\top x_1 \ne c^\top x_2$, then

$$|c^\top x_1 - c^\top x_2| > 2^{-2L}.$$

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)

## Proof depends on

- [Vertices of standard-form polyhedra have small denominators](vertices-of-standard-form-polyhedra-have-small-denominators.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 13, Theorem 17.
