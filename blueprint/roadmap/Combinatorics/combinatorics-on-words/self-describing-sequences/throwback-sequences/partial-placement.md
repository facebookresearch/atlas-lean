# Partial placement sequences

Let $X = (x_0, x_1, \dots)$ be a sequence of natural
numbers; the source takes $X$ strictly increasing with positive terms. The partial placement
sequences $P_n(X)$, for $n \ge 0$, are indexed by positions $z \in \mathbb{Z}$, and each
position is either empty or holds a term of $X$. $P_0(X)$ holds $x_0$ at the multiples of
$x_0 + 1$ and is empty elsewhere. $P_{n+1}(X)$ agrees with $P_n(X)$ at the filled positions of
$P_n(X)$ and fills some of its empty (open) positions with $x_{n+1}$, as follows. Let $s$ be
the least natural number that is an open position of $P_n(X)$ ($s = 0$ if there is none), and
let $d = x_{n+1} - (n + 1) + 1 = x_{n+1} - n$, an integer. An open position $z$ of $P_n(X)$
receives $x_{n+1}$ exactly when $d$ divides the signed number of open positions of $P_n(X)$
between $s$ and $z$, where open positions in $[s, z)$ count $+1$ and those in $[z, s)$ count
$-1$; all other open positions stay empty. When $d > 0$ and $P_n(X)$ has an open position
$\ge 0$, this places $x_{n+1}$ at $s$ and then, in both directions, at every $d$-th open
position.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Section 4.
