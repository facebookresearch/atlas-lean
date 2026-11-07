# Embedding of base phi expansions into Zeckendorf expansions

Let $\varphi$ be the golden
ratio and let $F_j$ be the Fibonacci numbers, $F_0 = 0$, $F_1 = F_2 = 1$. For a natural number $M$
let $Z(M)$ be the set of indices $i \ge 0$ such that $F_{i+2}$ occurs in the Zeckendorf
representation of $M$, so that $M = \sum_{i \in Z(M)} F_{i+2}$. Let $N$ be a natural number, let
$S$ be a base phi expansion of $N$ (the set of positions of its digits $1$), and let $s(N)$ be the
number of integers $n$ with $1 \le n \le N$ and $3 \lfloor n \varphi \rfloor + n + 1 < N$. Then
$\{i \in S : i \ge 0\} = Z(N + s(N))$.

Since $3 \lfloor n \varphi \rfloor + n + 1 > N$ for $n \ge N$, $s(N)$ is the number of all $n \ge 1$
with $3 \lfloor n \varphi \rfloor + n + 1 < N$, that is, the number of $M < N$ whose digit at
position $-1$ is $1$, as in the paper's proof. Both formulas for $s(N)$ printed in the paper are off
by one: $\max\{k : 3 \lfloor k \varphi \rfloor + k \le N\}$ gives $s(4) = 1$, but $Z(5) = \{3\}$
while $4 = \varphi^2 + 1 + \varphi^{-2}$ has nonnegative positions $\{0, 2\}$; and
$\max\{k : 3 \lfloor k \varphi \rfloor + k + 1 \le N\} - 1$ gives $s(6) = 0$, but
$Z(6) = \{0, 3\}$ while $6 = \varphi^3 + \varphi + \varphi^{-4}$ has nonnegative positions
$\{1, 3\}$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 1 (`integers-2024-A24-thm-1`).
