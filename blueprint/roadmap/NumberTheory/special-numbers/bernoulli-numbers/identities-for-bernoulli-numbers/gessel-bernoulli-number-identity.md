# Gessel's Bernoulli-number identity

Let $B_j$ denote the $j$-th Bernoulli number, with
$B_1 = -1/2$. For all natural numbers $n$, $r$ and $m$ with $r$ odd and $m \ge 1$,

$$\sum_{k=0}^{n+r} m^{n+r-k} \binom{n+r}{k} \binom{n+k+r}{r} B_{n+k} =
\frac{r+1}{2} \sum_{k=1}^{m-1} \sum_{j=0}^{r+1} \binom{n+r}{j} \binom{n+r}{r+1-j}
k^{j+n-1} (k-m)^{n+r-j}.$$

The powers on the right have integer exponents and nonzero rational bases: for $n = 0$ the terms
$j = 0$ and $j = r + 1$ have exponent $-1$.

## Sources

- Redha Chellal and Farid Bencherif, *An Identity for Generalized Bernoulli Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.11.2, formula `t5` (the special case `ℓ = n` with `r` odd), lines 142–149, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex>. Quoted there from H. Belbachir and M. Rahmani, *On Gessel-Kaneko's identity for Bernoulli numbers*, Appl. Anal. Discrete Math. 7 (2013), 1–10. Original: I. M. Gessel, *Applications of the classical umbral calculus*, Algebra Universalis 49 (2003), 397–434.
