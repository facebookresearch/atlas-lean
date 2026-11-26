# Real LWE experiment

Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a distinguisher map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a bit. The real LWE experiment draws $A \in \mathbb{Z}_q^{m \times n}$, the secret
$s \in \mathbb{Z}_q^n$ and the coins uniformly and the error $e \in \mathbb{Z}_q^m$ from
$\chi^m$, all independently, and outputs the distinguisher's bit on $(A, As + e)$ and the coins.

## Sources

- C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.3, case (1).
