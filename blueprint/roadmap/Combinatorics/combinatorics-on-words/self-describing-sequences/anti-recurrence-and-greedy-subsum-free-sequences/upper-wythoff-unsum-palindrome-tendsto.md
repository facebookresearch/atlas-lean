# The words $W_i$ converge to $3$ followed by the coded Fibonacci word

Let
$u_0 u_1 u_2 \cdots$ be the infinite Fibonacci word over $\{0, 1\}$, indexed from $0$, and let
$\mathbf{V}$ be the infinite word obtained from it by replacing each $0$ by $5$ and each
$1$ by $3$. Then the words $W_i$ of the unsum gap sequence converge to the infinite word
$3\mathbf{V}$: for every $k \ge 0$ there is $N$ such that for every $i \ge N$ the word $W_i$ has
more than $k$ digits and its digit at position $k$ (counted from zero) is the digit of
$3\mathbf{V}$ at position $k$, that is, $3$ if $k = 0$, and for $k \ge 1$ it is $3$ if
$u_{k-1} = 1$ and $5$ if $u_{k-1} = 0$.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Lemma 9 (`jis-2025-25.3.8-lem-9`).
