# Random LWE experiment

Let $n$ and $m$ be natural numbers and $q \ge 1$, and let a
distinguisher map a matrix in $\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins
in a finite nonempty set $S$ to a bit. The random LWE experiment draws
$A \in \mathbb{Z}_q^{m \times n}$, $u \in \mathbb{Z}_q^m$ and the coins uniformly and
independently, and outputs the distinguisher's bit on $(A, u)$ and the coins.

## Sources

- C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.3, case (2).
