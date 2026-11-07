# Alternating sum of shifted binomial coefficients

Let $\ell$, $n$, $j$ and $s$ be natural
numbers with $1 \le \ell \le n$, $j \ge 1$ and $\ell j + s \le n$. Then

$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} \binom{n-i}{\ell j+s} = \binom{n-\ell}{\ell(j-1)+s}.$$

The paper states this for $\lfloor (1-s)/\ell \rfloor \le j \le \lfloor (n-s)/\ell \rfloor$; only
$j \ge 1$ is stated here, since for $j \le 0$ the right side can have a negative lower index. For
$j \ge 1$ the bound $j \le \lfloor (n-s)/\ell \rfloor$ is the condition $\ell j + s \le n$.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Lemma 4.1 (`fq-2024-florez11012023-lem-4.1`).
