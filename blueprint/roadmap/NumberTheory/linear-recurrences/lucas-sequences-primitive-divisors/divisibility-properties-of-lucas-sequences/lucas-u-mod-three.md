# Lucas sequences modulo 3

Let $U = U(P, Q)$ be the Lucas sequence with integer parameters
$P$ and $Q \ne 0$, let $D = P^2 - 4Q$, and suppose $3 \nmid \gcd(P, Q)$. Then $U$ is periodic
modulo $3$ from index $1$ on: there is $k > 0$ with $U_{n+k} \equiv U_n \pmod 3$ for every
$n \ge 1$. If $3 \mid Q$, then $3 \nmid U_n$ for every $n \ge 1$. If $3 \mid P$, then for every
$n \ge 0$, $3 \mid U_n$ if and only if $2 \mid n$. If $3 \nmid P$ and $Q \equiv -1 \pmod 3$,
then for every $n \ge 0$, $3 \mid U_n$ if and only if $4 \mid n$. If $3 \nmid P$ and
$Q \equiv 1 \pmod 3$, then for every $n \ge 0$, $3 \mid U_n$ if and only if $3 \mid n$; moreover
$3 \mid D$.

The periodicity need not start at $n = 0$: for $P = 1$ and $Q = 3$, $U$ is $0, 1, 1, 1, \dots$
modulo $3$. The source's values $\rho(3) = 2, 4, 3$ of the rank of apparition are the least
positive indices these equivalences give.

## Sources

- Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*, INTEGERS 25 (2025), Article A107, Lemma 2.8 (`integers-2025-A107-lem-2-8`).
