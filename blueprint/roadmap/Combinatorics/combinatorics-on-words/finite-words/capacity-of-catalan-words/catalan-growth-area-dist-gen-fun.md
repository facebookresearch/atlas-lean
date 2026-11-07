# Area generating function of words with unit-bounded rises, by first letter

For natural
numbers $i$ and $j$ with $1 \le i \le j$ and for $n \ge 0$, let $c(n, j, i; q) \in \mathbb{Z}[q]$
be the area distribution of the words of length $n$ with letters in $\{1, \dots, j\}$, each letter
at most one more than the letter before it, that begin with $i$ and end with $j$: the sum of
$q^{\mathrm{area}(w)}$ over these words $w$, where $\mathrm{area}(w)$ is the sum of the letters
of $w$. Let $d_0, d_1, \dots$ be the power series in $x$ over $\mathbb{Z}[q]$ defined by
$d_0 = 1$, $d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and
$d_k = (1 - xq^k)\, d_{k-1} - x^2 q^{2k-1} d_{k-3}$ for $k \ge 3$; each $d_k$ has constant term
$1$, so it is invertible. Then, as formal power series in $x$ over $\mathbb{Z}[q]$,

$$\sum_{n \ge 0} c(n, j, i; q)\, x^n =
x^{j-i+1} q^{\binom{j+1}{2} - \binom{i}{2}}\, \frac{d_{i-1}(x; q)}{d_j(x; q)}.$$

The term for $n = 0$ is zero, since there are no words of length $0$ that end with $j$.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3 (`integers-2025-A5-lem-3`).
