# Reduction of a double binomial absolute-value sum

For all natural numbers $\beta$, $m$ and
$n$,

$$\sum_{i=0}^{2m} \sum_{j=0}^{2n} \binom{2m}{i} \binom{2n}{j} \lvert (i-m)-(j-n) \rvert^{\beta}
= \sum_{k=0}^{2(m+n)} \binom{2(m+n)}{k} \lvert k-m-n \rvert^{\beta},$$

with the convention $0^0 = 1$.

In the source's notation, $S_\beta(n) = \sum_k \binom{2n}{n+k} \lvert k \rvert^\beta$ and
$T_\beta(m,n) = \sum_{k,\ell} \binom{2m}{m+k} \binom{2n}{n+\ell} \lvert k-\ell \rvert^\beta$, and
the identity reads $T_\beta(m,n) = S_\beta(m+n)$, after the shift $i = m + k$, $j = n + \ell$.

## Sources

- Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, and Helmut Prodinger, "Some Binomial Sums Involving Absolute Values," Journal of Integer Sequences 19 (2016), Article 16.3.7, Theorem, lines 278–283 (with `S_β` defined at lines 245–247 and `T_β` at 271–274), https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
