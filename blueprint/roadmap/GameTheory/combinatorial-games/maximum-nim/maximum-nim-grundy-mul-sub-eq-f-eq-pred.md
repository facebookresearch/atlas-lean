# Floor-rule Maximum Nim: one-step Grundy reduction when k = nt + h

Let $n$, $t$, $h$ be
natural numbers with $t \ge 1$ and $1 \le h \le n$, and let $k = nt + h$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$, and let $F(x) = \lfloor (k-1)x/k \rfloor$. Then for every natural
number $i$ with $1 \le i \le n$,

$$G(nk - i) = G(F(nk - i)) = G(n(k - 1) - i).$$

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Lemma 5(ii.1) (`integers-2024-G5-lem-5`).
