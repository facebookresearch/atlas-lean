# Floor-rule Maximum Nim: Grundy reduction when $n = kt + u$

Let $k$, $t$, $u$ and $n$ be
natural numbers with $k \ge 2$, $t \ge 1$, $u \le k - 1$ and $n = kt + u$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$. Then for every natural number $i$ with $1 \le i \le n$ that is not
divisible by $k$,

$$G(nk - i) = G\bigl((n - t)k - (u + i - \lfloor i/k \rfloor)\bigr).$$

The hypotheses force $i \le nk$ and $u + i - \lfloor i/k \rfloor \le (n - t)k$, so all
subtractions are ordinary differences of natural numbers. The right side is read with the
parentheses shown; read without them, as in the extracted statement, the equality is false.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Lemma 5(i).
