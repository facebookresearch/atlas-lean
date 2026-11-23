# The omega homomorphism on symmetric polynomials

Let $R$ be a commutative ring and let $V$
be a finite set with $n$ elements. A polynomial in $R[x_v : v \in V]$ is symmetric if it is
unchanged by every permutation of the variables. For $k \ge 0$, the elementary symmetric polynomial
$e_k$ is the sum of $\prod_{v \in T} x_v$ over all $k$-element subsets $T \subseteq V$, and the
complete homogeneous symmetric polynomial $h_k$ is the sum of $\prod_{v \in M} x_v$ over all
multisets $M$ of size $k$ with elements from $V$, each element counted with its multiplicity.
Every symmetric polynomial $f$ equals $P(e_1, \dots, e_n)$ for exactly one polynomial
$P \in R[y_1, \dots, y_n]$. The omega homomorphism $\omega$ is the $R$-algebra homomorphism from the
symmetric polynomials in $R[x_v : v \in V]$ to themselves given by
$\omega(P(e_1, \dots, e_n)) = P(h_1, \dots, h_n)$; equivalently, it is the unique $R$-algebra
homomorphism with $\omega(e_k) = h_k$ for $1 \le k \le n$.
