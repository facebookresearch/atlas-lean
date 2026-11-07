# Gudmundsson's bijection between Dyck words and standard Young tableaux

For every $n$
there is a map $f$ from Dyck words to semistandard Young tableaux of the two-row shape $(n, n)$
with the following two properties. First, for every Dyck word $w$ of semilength $n$ and every
$i \ge 1$, if the $i$th letter of $w$ is an up step $U$ then $i$ is an entry of the first row of
$f(w)$, and if it is a down step $D$ then $i$ is an entry of the second row. Second, $f$
restricts to a bijection from the Dyck words of semilength $n$ onto the standard tableaux of
shape $(n, n)$, that is, those whose $2n$ entries are distinct and lie in $\{1, \dots, 2n\}$.

Since $f(w)$ is standard, $i$ lies in the first row of $f(w)$ exactly when the $i$th letter of $w$
is $U$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 22 (Gudmundsson, Theorem 6) (`jis-2024-24.8.6-lem-22`).
