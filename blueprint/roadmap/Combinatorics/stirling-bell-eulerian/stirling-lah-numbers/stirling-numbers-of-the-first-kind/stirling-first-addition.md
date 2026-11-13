# Addition formula for Stirling numbers of the first kind

Write $c(n,k)$ for the unsigned
Stirling numbers of the first kind and $u^{\overline{i}} = u(u+1)\cdots(u+i-1)$ for the rising
factorial. For all natural numbers $u$, $v$ and $k$,

$$c(u+v,k) = \sum_{j=0}^{v} \sum_{i=0}^{v} \binom{v}{i}\, u^{\overline{i}}\, c(v-i,j)\, c(u,k-j),$$

where a term with $j > k$ is read as $0$.

## Sources

- Grzegorz Rządkowski, "Two Formulas for Successive Derivatives and Their Applications," Journal of Integer Sequences 12 (2009), Article 09.8.2, Theorem, equation (ex44), lines 257–263, https://cs.uwaterloo.ca/journals/JIS/VOL12/Rzadkowski/rzadkowski3.tex
