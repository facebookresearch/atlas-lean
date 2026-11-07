# Odd-index binomial sum with inverse generalized binomial coefficients

Write $\binom{u}{w} = \Gamma(u+1)/(\Gamma(w+1)\Gamma(u-w+1))$ for the generalized binomial
coefficient of complex $u$, $w$, which for natural $u$, $w$ is the ordinary binomial coefficient.
For every natural number $n$ and every real $v > -1$,

$$
\sum_{k=1}^{\lceil n/2 \rceil} \binom{n}{2k-1} \frac{2^n}{2^{2k}} \binom{2k}{k}
\binom{(2k+v)/2}{k}^{-1}
= \frac{1}{2} \binom{2n+v+2}{(2n+v+2)/2} \binom{n+v+1}{v/2}^{-1} -
\binom{2n+v}{(2n+v)/2} \binom{n+v}{v/2}^{-1}.
$$

This is equation (17) of the source, the case $n = 1$ of its two-parameter identity (14), whose
parameter $m$ is called $n$ here.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Corollary 2 (`integers-2026-A19-cor-2`).
