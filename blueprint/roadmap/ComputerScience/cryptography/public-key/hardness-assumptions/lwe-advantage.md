# Decision LWE advantage

Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a distinguisher $D$ map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a bit. Its decision LWE advantage is the real number
$|p_{\mathrm{real}} - p_{\mathrm{rand}}|$, where $p_{\mathrm{real}}$ and $p_{\mathrm{rand}}$ are
the probabilities that $D$ outputs $1$ in the real and in the random LWE experiment.

## Sources

- C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.3; O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*, J. ACM 56(6) (2009), Article 34, Section 2.
