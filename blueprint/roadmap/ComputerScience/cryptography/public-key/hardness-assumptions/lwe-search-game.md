# Search LWE experiment

Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a solver map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a vector in $\mathbb{Z}_q^n$. The search LWE experiment draws $A \in \mathbb{Z}_q^{m \times n}$,
the secret $s \in \mathbb{Z}_q^n$ and the coins uniformly and the error $e \in \mathbb{Z}_q^m$
from $\chi^m$, all independently, gives the solver $(A, As + e)$ and the coins, and outputs $1$
when the solver's output equals $s$.

## Sources

- C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.2, with the $m$ samples as the rows of $A$; O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*, J. ACM 56(6) (2009), Article 34, Section 1.
