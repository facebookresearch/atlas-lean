# Dyck words and nondecreasing parking functions

For every $n$ there is a map $g$ from Dyck
words to maps $\{0, \dots, n-1\} \to \{0, \dots, n-1\}$ such that, for every Dyck word $w$ of
semilength $n$ and every $i < n$, $g(w)(i)$ is the number of down steps $D$ of $w$ before its
$(i+1)$st up step $U$, and $g$ restricts to a bijection from the Dyck words of semilength $n$
onto the nondecreasing parking functions of length $n$.

With one-based entries, the $i$th entry of the parking function is one plus the number of $D$s
before the $i$th $U$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 23 (`jis-2024-24.8.6-lem-23`).
