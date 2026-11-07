# Toeplitz–Hessenberg determinants with Oresme entries

For numbers $a_0, a_1, \dots, a_n$,
let $\det(a_0; a_1, \dots, a_n)$ be the determinant of the $n \times n$ matrix whose $(i, j)$
entry is $a_{i-j+1}$ if $j \le i + 1$ and $0$ otherwise, so that $a_0$ fills the superdiagonal.
Let $O_k = k/2^k$ be the Oresme numbers, $F_n$ the Fibonacci numbers, $L_n$ the Lucas numbers,
$P_n$ the Pell numbers, $Q_n$ the Pell–Lucas numbers ($Q_0 = Q_1 = 2$) and $J_n$ the Jacobsthal
numbers, the Lucas sequence $U(1, -2)$ ($J_0 = 0$, $J_1 = 1$, $J_{k+2} = J_{k+1} + 2J_k$). Then
for every $n \ge 1$ the following hold in $\mathbb{Q}$:
(19) $\det(-2; O_2, \dots, O_{n+1})$ equals $5^{(n-1)/2} F_{n+1}/2^n$ for odd $n$ and
$5^{(n-2)/2} L_{n+1}/2^n$ for even $n$;
(20) $\det(-4; O_0, \dots, O_{n-1})$ equals $2^{(n+1)/2} P_{n-1}$ for odd $n$ and
$2^{(n-2)/2} Q_{n-1}$ for even $n$;
(21) $\det(-1/2; O_2, \dots, O_{n+1})$ equals $P_{n+1}/2^{(3n+1)/2}$ for odd $n$ and
$Q_{n+1}/2^{(3n+4)/2}$ for even $n$;
(22) $\det(1/4; O_3, \dots, O_{n+2}) = F_{n+3}/2^{3n}$;
(23) $\det(-1/8; O_4, \dots, O_{n+3}) = F_{2n+4}/2^{3n+2}$;
(24) $\det(1/4; O_3, O_5, \dots, O_{2n+1}) = F_{3n+1}/2^{4n-1}$;
(25) $\det(1/4; O_5, O_7, \dots, O_{2n+3}) = J_{n+3}/2^{5n}$;
(26) $\det(-2; O_1, \dots, O_n) = J_{2n}/2^n$;
(27) $\det(-1/4; O_1, \dots, O_n) = P_{2n}/2^{3n-1}$.

The exponents of (20) are typeset $2^{(n+1/2)}$ and $2^{(n-2/2)}$ in the source; they are read as
$2^{(n+1)/2}$ and $2^{(n-2)/2}$, since the literal $2^{n+1/2}$ is irrational while the
determinant is rational (for $n = 3$ the determinant is $8 = 2^2 P_2$).

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 4 (`integers-2025-A97-cor-4`).
