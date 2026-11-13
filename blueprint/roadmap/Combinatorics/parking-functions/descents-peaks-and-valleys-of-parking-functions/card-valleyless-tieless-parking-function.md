# Valleyless-tieless parking functions are counted by the Fine numbers

Write a parking
function $f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. It is
valleyless-tieless if there is no $j$ with $a_{j-1} > a_j < a_{j+1}$ (a valley) and no $j$ with
$a_j = a_{j+1}$ (a tie). For every $n \ge 1$, the number of valleyless-tieless parking functions
of length $n$ is the Fine number $F(n+1)$, where the Fine numbers are indexed from $0$ with
$F(0) = 1$; for $n = 1, \dots, 5$ these counts are $1, 2, 6, 18, 57$.

In the offset-0 indexing of OEIS A000957 ($0, 1, 0, 1, 2, 6, 18, \dots$), $F(n+1)$ is the term
of index $n + 2$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 33 (`jis-2024-24.8.6-thm-33`).
