# Period of a Lucas sequence modulo $m$

For a Lucas sequence $U = U(P, Q)$ and a natural
number $m$, the least period $\pi_U(m)$ of $U$ modulo $m$ is the minimal period of the pair
$(0, 1)$ under the map $(x, y) \mapsto (y, P y - Q x)$ on pairs of residues modulo $m$, that is,
the least $r > 0$ with $U_r \equiv 0 \pmod m$ and $U_{r+1} \equiv 1 \pmod m$, and $0$ if there
is no such $r$.

For $m > 0$, $\pi_U(m) = 0$ exactly when $U$ is not purely periodic modulo $m$, that is, when
$\gcd(m, Q) > 1$. For $m = 0$ the residues are integers and the congruences are equalities; this
value has no meaning in the paper (for the Fibonacci sequence it is $0$).

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 1, equation (1.11).
