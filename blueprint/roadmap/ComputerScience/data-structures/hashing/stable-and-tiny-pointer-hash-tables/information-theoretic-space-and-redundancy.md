# Information-theoretic space bound and redundancy of a dictionary

A dictionary storing a set $S \subseteq U$ with $|S| = n$ must use at least $\mathcal{B}(U, n) = \left\lceil \log_2 \binom{|U|}{n} \right\rceil$ bits in the worst case. A structure using $\mathcal{B}(U, n) + r$ bits has *redundancy* $r$; it is *succinct* if $r = o(\mathcal{B}(U, n))$. When $|U| = n^{c}$ for a constant $c > 1$, $\mathcal{B}(U, n) = (c - 1)\, n \log_2 n + O(n)$.

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6) (2023), arXiv:2109.04548.
- Erik D. Demaine, Friedhelm Meyer auf der Heide, Rasmus Pagh, Mihai Pătraşcu, "De Dictionariis Dynamicis Pauco Spatio Utentibus", LATIN (2006).
