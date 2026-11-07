# Symbolic recurrence for Carlitz-type sequences

Let $q > 0$ with $q \ne 1$, write
$[x] = (q^x - 1)/(q - 1)$, let $r$ be a natural number, let $P$ be a real polynomial and let
$(a_k)$ be a real sequence with $[k + r]\, a_k = P(k)$ for every natural number $k$. If $(T_n)$ is
a Carlitz-type sequence with associated sequence $(a_k)$ and $t_n = T_n(0)$, then for every natural
number $n$ greater than the degree of $P$ (taken to be $0$ when $P = 0$),
$q^r \sum_{j=0}^{n} \binom{n}{j} q^j t_j = t_n$, which in umbral notation reads
$q^r (q t + 1)^n = t^n$.

The hypothesis $[k + r]\, a_k = P(k)$ encodes $a_k = P(k)/[k + r]$; for $r = 0$ it forces
$P(0) = 0$ and leaves $a_0$ free.

## Sources

- Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.5 (`integers-2026-A85-thm-2-5`).
