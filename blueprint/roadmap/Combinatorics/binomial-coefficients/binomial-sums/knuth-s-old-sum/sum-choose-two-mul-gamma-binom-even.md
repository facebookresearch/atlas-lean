# Even-index identity for generalized central binomial coefficients

Write $\binom{u}{w} = \Gamma(u+1)/(\Gamma(w+1)\Gamma(u-w+1))$ for the generalized binomial
coefficient of complex $u$, $w$, which for natural $u$, $w$ is the ordinary binomial coefficient.
For every natural number $n$ and every real $v > -1$,

$$
\sum_{k=0}^{n} \binom{2n}{2k} \binom{2(n-k)}{n-k} \binom{2k+v}{(2k+v)/2}
\binom{(2n+v)/2}{n-k}^{-1}
= \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} 2^{2n-2k} \binom{2k}{k}
\binom{2k+v}{(2k+v)/2} \binom{(4k+v)/2}{k}^{-1}.
$$

This is equation (56) of the source.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 19 (`integers-2026-A19-thm-19`).
