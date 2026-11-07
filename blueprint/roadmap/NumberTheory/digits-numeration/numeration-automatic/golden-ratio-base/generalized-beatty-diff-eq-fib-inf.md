# First differences of a generalized Beatty sequence

Let $\varphi$ be the golden ratio, for
integers $p, q, r$ let $V(p, q, r)$ be the sequence $n \mapsto p\lfloor n\varphi \rfloor + qn + r$
on the natural numbers, and let $x_0 x_1 x_2 \cdots$ be the infinite Fibonacci word. For all
integers $p, q, r$ and every $n \ge 1$, the difference $V(p, q, r)(n+1) - V(p, q, r)(n)$ equals
$p + q$ if $x_{n-1} = 1$ and $2p + q$ if $x_{n-1} = 0$. Conversely, for all integers $a, b$ and
every sequence $v$ of integers indexed by the natural numbers such that, for every $n \ge 1$,
$v(n+1) - v(n)$ equals $b$ if $x_{n-1} = 1$ and $a$ if $x_{n-1} = 0$, there is an integer $r'$
with $v(n) = V(a - b, 2b - a, r')(n)$ for every $n \ge 1$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Lemma 5.
