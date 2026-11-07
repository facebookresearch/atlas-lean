# Sum formula for anassas below the diagonal

Let $A(m, k, p)$ be the number of
nonattacking placements of $k$ anassas on the square board $\{1, \dots, m\}^2$ with exactly $p$
of them strictly below the main diagonal, and let ${n \brace j}$ be Knuth's extended Stirling
numbers of the second kind. For natural numbers $m$, $k$, $p$ with $p \le k$,

$$A(m, k, p) = \sum_{j=0}^{p} (m-k+j)_j \binom{k-p-1}{j} \binom{k-j}{k-p}
{m+1 \brace m-k+j+1}$$

in the integers, where $(x)_j = x(x-1)\cdots(x-j+1)$ is the falling factorial and
$\binom{k-p-1}{j}$ is the generalized binomial coefficient, so that $\binom{-1}{j} = (-1)^j$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`).
