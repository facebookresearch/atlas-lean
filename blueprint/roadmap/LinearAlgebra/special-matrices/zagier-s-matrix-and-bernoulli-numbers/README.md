# Zagier's matrix conjecture

Let $K$ be a natural number and let $B_n$ be the Bernoulli numbers, with $B_1 = -\tfrac12$ and $\binom{m}{k} = 0$ for $k > m$. Let $A$, $P$ and $Q$ be the $(K-1) \times (K-1)$ rational matrices, indexed by $1 \le i, j \le K - 1$, with

$$A_{ij} = \binom{2K - 2j}{2i - 1} + \binom{2K - 2j}{2K - 2i}, \qquad P_{ij} = \frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2j-1}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$

and $Q_{ij} = -\frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2K-2j}{2K-2i-n+1} \binom{n+2i-2}{n} B_n$. Then $P = Q$, $AP = I$ and $PA = I$.

## Idea

The matrix $A$ has simple binomial entries, and Zagier conjectured that its inverse is given explicitly by Bernoulli numbers. The conjecture offers two formulas, $P$ and $Q$, and asserts that they agree and that they invert $A$ on both sides. For small $K$ it can be checked by hand: for $K = 2$, $A$ is the $1 \times 1$ matrix $\binom{2}{1} + \binom{2}{2} = 3$ and $P_{11} = 2\bigl(\binom{1}{3}B_0 + \binom{1}{2}B_1 + \binom{1}{1}B_2\bigr) = 2B_2 = \tfrac13$. Several proofs are known, among them one by Ma and Teo.

## Statements

- [Zagier's matrix conjecture](zagier-matrix-inverse.md)
- [Zagier's matrix](zagier-matrix.md): the matrix $A$
- [First Bernoulli formula for the inverse of Zagier's matrix](zagier-inverse-p.md): the first Bernoulli formula $P$
- [Second Bernoulli formula for the inverse of Zagier's matrix](zagier-inverse-q.md): the second Bernoulli formula $Q$
- [The two Bernoulli formulas for the inverse of Zagier's matrix agree](zagier-inverse-p-eq-zagier-inverse-q.md): $P = Q$
- [Left inverse of Zagier's matrix](zagier-inverse-p-mul-zagier-matrix.md): $PA = I$
- [Right inverse of Zagier's matrix](zagier-matrix-mul-zagier-inverse-p.md): $AP = I$
