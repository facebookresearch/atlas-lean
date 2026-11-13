# Peakless parking functions with $n - 2$ ties

For every $n \ge 2$, the number of parking
functions $(a_1, \dots, a_n)$ of length $n$ that have no peaks (no $i$ with $a_{i-1} < a_i$ and
$a_i > a_{i+1}$) and exactly $n - 2$ ties (indices $i \in \{1, \dots, n - 1\}$ with
$a_i = a_{i+1}$) is $(n - 1)n$.

The paper prints $n(n + 1)$, which contradicts its own table ($2, 6, 12, 20, 30$ for
$n = 2, \dots, 6$); its proof counts tuples with $i$ leading ones followed by $n - i \ge 1$
copies of one value, so $1 \le i \le n - 1$ and each monotone direction contributes
$\sum_{i=1}^{n-1} i$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 43 (`jis-2024-24.8.6-lem-43`).
