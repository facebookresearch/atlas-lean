# A pseudorandom permutation is a pseudorandom function

Let $F$ be a keyed permutation of a finite nonempty set $X$, and let a distinguisher with uniform coins
make at most $q$ queries. Its PRF advantage against $k \mapsto F_k$ is at most its PRP advantage
against $F$ plus the probability that $q$ independent uniform samples from $X$ are not all distinct,
which is at most $q(q - 1)/(2|X|)$ (Katz and Lindell, Section 3.5.1).
