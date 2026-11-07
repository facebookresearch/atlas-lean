# Valley plateaus of a uniquely encoded parking function equal $1$

For a map
$g : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$, its statistic encoding is the word of length
$n - 1$ whose $k$-th letter, for $1 \le k \le n - 1$, is $<$, $=$ or $>$ according as
$g(k-1) < g(k)$, $g(k-1) = g(k)$ or $g(k-1) > g(k)$. Let $f$ be a parking function of length $n$
such that every parking function of length $n$ with the same statistic encoding as $f$ equals
$f$, and write $\alpha_k = f(k-1) + 1$ for $1 \le k \le n$. If $2 \le i \le j \le n - 1$,
$\alpha_{i-1} > \alpha_i$, $\alpha_k = \alpha_i$ for every $k$ with $i \le k \le j$, and
$\alpha_j < \alpha_{j+1}$, then $\alpha_k = 1$ for every $k$ with $i \le k \le j$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 51 (`jis-2024-24.8.6-lem-51`).
