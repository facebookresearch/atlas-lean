# Prepending $1$ to valleyless-tieless parking functions

Identify a parking function $f$
of length $m$ with the word $(f(0) + 1, \dots, f(m-1) + 1)$. A word $(a_1, \dots, a_m)$ has a
tie if $a_k = a_{k+1}$ for some $k$, and a valley if $a_{k-1} > a_k < a_{k+1}$ for some $k$;
write $\mathrm{VTPF}_m$ for the set of parking functions of length $m$ with no ties and no
valleys. For $n \ge 1$, the map $(a_1, \dots, a_n) \mapsto (1, a_1 + 1, \dots, a_n + 1)$ is a
bijection from $\mathrm{VTPF}_n$ onto the set of $(b_1, \dots, b_{n+1}) \in \mathrm{VTPF}_{n+1}$
with $b_1 = 1$ and $b_{n+1} > 1$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 34 (`jis-2024-24.8.6-lem-34`).
