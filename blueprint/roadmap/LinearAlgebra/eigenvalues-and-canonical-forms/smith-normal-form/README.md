# Smith normal form

Let $R$ be a principal ideal domain, $M$ a finitely generated free $R$-module and $N$ a submodule of $M$. Then there are natural numbers $n \le m$, a basis $e_0, \dots, e_{m-1}$ of $M$, a basis $f_0, \dots, f_{n-1}$ of $N$ and nonzero $a_0, \dots, a_{n-1} \in R$ such that $f_i = a_i e_i$ for every $i < n$ and $a_i \mid a_{i+1}$ whenever $i + 1 < n$.

## Idea

In matrix language, every matrix over a principal ideal domain can be brought by invertible row and column operations to a diagonal matrix whose diagonal entries divide each other. Over $\mathbb{Z}$ the operations are those of Gaussian elimination with integer multipliers, combined with the Euclidean algorithm to make the corner entry divide the others. The theorem gives aligned bases of a free module and of any submodule. Applied to a presentation of a finitely generated module, it proves the structure theorem: a finitely generated abelian group is $\mathbb{Z}^r \oplus \mathbb{Z}/a_0 \oplus \dots \oplus \mathbb{Z}/a_{n-1}$ with $a_0 \mid a_1 \mid \cdots$. Over $K[x]$ it gives the rational canonical form of a matrix.

## Statements

- [Smith normal form](smith-normal-form.md)
- [Smith normal form with a divisibility chain](exists-smith-normal-form-dvd-chain.md): the same statement under its descriptive name; the main statement is derived from it
