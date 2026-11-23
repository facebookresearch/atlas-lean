# Uniformly recurrent sequence

A sequence $s : \mathbb{N} \to \alpha$ is uniformly
recurrent if for every factor $w$ there is a constant $C_w$ such that every occurrence of $w$ is
followed by another occurrence at distance at most $C_w$: for all $i, \ell \in \mathbb{N}$ there
is $C \in \mathbb{N}$ such that for every $i'$ with $s(i' + t) = s(i + t)$ for all $t < \ell$,
there is $j$ with $0 < j \le C$ and $s(i' + j + t) = s(i + t)$ for all $t < \ell$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Definition 1.
