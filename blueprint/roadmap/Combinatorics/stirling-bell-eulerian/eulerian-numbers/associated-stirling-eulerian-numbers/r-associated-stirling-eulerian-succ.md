# Convolution recurrence for the $r$-associated Stirling Eulerian numbers

For natural
numbers $r$, $n$, $m$ let $A^r_{n,m}$ be the number of permutations $\sigma$ of
$\{0, \dots, n-1\}$ with exactly $m$ excedances (points $i$ with $\sigma(i) > i$) all of whose
cycles (fixed points counted as cycles of length one) have length greater than $r$, and for
natural numbers $a$, $b$ let $C_{a,b}$ be the circular Eulerian number, the number of
permutations of $\{0, \dots, a-1\}$, $a \ge 1$, that consist of a single cycle through all
points and have exactly $b$ excedances ($C_{0,b} = 0$). If $r \ge 1$, $m \le n$ and
$n \ge r + 1$, then

$$A^r_{n+1,m} = \sum_{j=r}^{n} \binom{n}{j} \sum_{i=1}^{m} C_{j+1,i} A^r_{n-j,m-i}.$$

The hypothesis $r \ge 1$ is needed: for $r = 0$, $n = 1$, $m = 0$ the left side is
$A^0_{2,0} = 1$ (the identity) while the right side is $0$, every inner sum over $1 \le i \le 0$
being empty.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 31 (`jis-2025-25.5.7-thm-31`).
