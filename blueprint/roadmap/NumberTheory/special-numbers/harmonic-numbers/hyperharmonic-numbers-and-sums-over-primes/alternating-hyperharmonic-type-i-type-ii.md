# Explicit formulas for type I and type III alternating hyperharmonic numbers

For real $s$
write $H_n^{(s)} = \sum_{i=1}^{n} 1/i^s$ and $\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$
for the generalized and the alternating generalized harmonic numbers. For a natural number $p$,
the type I and type III generalized alternating hyperharmonic numbers are
$H_n^{(p,1,1)} = H_n^{(p)}$, $H_n^{(p,1,3)} = \overline{H}_n^{(p)}$ and, for $i = 1, 3$,
$H_n^{(p,r+1,i)} = \sum_{k=1}^{n} (-1)^{k-1} H_k^{(p,r,i)}$. Let $b_1(r, j, m, k)$ for
$k = 0, 1, 2, 3$ be Li's rational coefficients. Then for all natural numbers $r, n, p \ge 1$,
with $g = \lfloor (r-1)/2 \rfloor$ and $\varepsilon_n = (-1)^{n-1}$,

$$
H_n^{(p,r,1)} = \sum_{m=0}^{g} \sum_{j=0}^{g-m} \bigl(b_1(r,j,m,0)\,\varepsilon_n H_n^{(p-m)} +
b_1(r,j,m,1)\,\overline{H}_n^{(p-m)} + b_1(r,j,m,2)\,H_n^{(p-m)} +
b_1(r,j,m,3)\,\varepsilon_n \overline{H}_n^{(p-m)}\bigr)\, n^j
$$

and

$$
H_n^{(p,r,3)} = \sum_{m=0}^{g} \sum_{j=0}^{g-m} \bigl(b_1(r,j,m,0)\,\varepsilon_n
\overline{H}_n^{(p-m)} + b_1(r,j,m,1)\,H_n^{(p-m)} + b_1(r,j,m,2)\,\overline{H}_n^{(p-m)} +
b_1(r,j,m,3)\,\varepsilon_n H_n^{(p-m)}\bigr)\, n^j,
$$

where the index $p - m$ is a real number and may be negative.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Lemma 6 (`jis-2024-24.4.1-lem-6`).
