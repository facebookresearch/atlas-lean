# Peakless-tieless parking functions by last entry

Write a parking function $f$ of length
$n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1 \in \{1, \dots, n\}$. It is
peakless-tieless if there is no $j$ with $a_{j-1} < a_j > a_{j+1}$ (a peak) and no $j$ with
$a_j = a_{j+1}$ (a tie). For natural numbers $i$ and $n$ with $1 \le i \le n$, the number of
peakless-tieless parking functions of length $n$ with last entry $a_n = i$ is

$$\binom{n+i-2}{i-1} \cdot \frac{n-i+1}{n}.$$

This is the Catalan-triangle entry $T(n-1, i-1)$ of OEIS A009766.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 32 (`jis-2024-24.8.6-cor-32`).
