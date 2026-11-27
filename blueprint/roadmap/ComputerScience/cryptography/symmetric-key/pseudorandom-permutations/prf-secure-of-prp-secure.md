# A PRP family is a PRF family

Suppose every admissible distinguisher family makes polynomially many queries and, for every
polynomial $p$, the probability that $p(n)$ independent uniform samples from $X_n$ are not all
distinct is negligible in $n$ (for example when $|X_n| = 2^n$; stated here without proof). Then
every family of keyed permutations that is PRP-secure relative to the class is PRF-secure relative
to it (Katz and Lindell, Section 3.5.1).
