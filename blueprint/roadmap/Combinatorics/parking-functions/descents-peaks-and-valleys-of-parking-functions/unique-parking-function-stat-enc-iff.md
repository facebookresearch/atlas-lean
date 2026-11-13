# Statistic encodings with a unique parking function

The statistic encoding of a parking
function $(a_1, \dots, a_n)$ is the word $w_1 \cdots w_{n-1}$ over $\{A, D, T\}$ with $w_i = A$ if
$a_i < a_{i+1}$, $w_i = D$ if $a_i > a_{i+1}$ and $w_i = T$ if $a_i = a_{i+1}$. For every
$n \in \mathbb{N}$, a word over $\{A, D, T\}$ with one letter for each $1 \le i \le n - 1$ is the
statistic encoding of exactly one parking function of length $n$ if and only if it consists of
$A$'s followed by $T$'s or of $T$'s followed by $D$'s (either block may be empty).

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 52 (`jis-2024-24.8.6-thm-52`).
