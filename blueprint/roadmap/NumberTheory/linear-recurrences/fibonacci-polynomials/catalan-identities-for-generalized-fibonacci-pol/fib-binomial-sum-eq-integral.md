# Binomial sum of Fibonacci numbers as an integral

Let $F \colon \mathbb{Z} \to \mathbb{R}$
be a function whose value $F_m$ at every $m \ge 0$ is the $m$-th Fibonacci number (with $F_0 = 0$
and $F_1 = 1$) and which satisfies $F_{m+2} = F_{m+1} + F_m$ for every integer $m$. Then for every
real $k \ge 2$ and every integer $n \ge 1$,

$$\sum_{i=0}^{n} (-1)^{n+1} \binom{n}{i} (k+1)^i (k-1)^{n-i} F_{n-2i}
  = n \int_{-k}^{k} (\sqrt{5}\, y + 1)^{n-1} \, dy.$$

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Corollary 5.2 (`fq-2024-florez11012023-cor-5.2`).
