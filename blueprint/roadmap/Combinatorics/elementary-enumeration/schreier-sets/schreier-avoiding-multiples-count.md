# Schreier sets avoiding multiples

For natural numbers $u$ and $n$, let $G_{u,n}$ be the
set of the first $n$ positive integers not divisible by $u$ (taken to be empty when $u = 0$), and
call a finite set $F$ of natural numbers Schreier when every element of $F$ is at least $|F|$.
Then $|D_{u,n}|$ is the number of Schreier sets $F \subseteq G_{u,n}$ with
$\lfloor (un - 1)/(u - 1) \rfloor \in F$.

For $u \le 1$ or $n = 0$ the set $G_{u,n}$ is empty and the count is $0$; otherwise $un - 1$ and
$u - 1$ are positive, so the natural-number subtraction and floor division agree with the real
expression.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Section 1 (definition of `D_{u,n}`).
