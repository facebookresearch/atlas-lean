# Intersection of Hamming spheres

Let $H^l_\alpha = \{1,\dots,\alpha\}^l$ be the space of sequences of length $l$ over an alphabet of $\alpha \ge 2$ letters with Hamming distance $d_H$, and let $S(a,r) = \{b : d_H(a,b) = r\}$. Let $a, c \in H^l_\alpha$ with $d_H(a,c) = n$ and let $r \le m$ (the other case is symmetric). Then

$$\bigl|S(a,r) \cap S(c,m)\bigr| = \sum_{\substack{r_+ + r_- + r_0 = r\\ r_+ - r_- = n - m\\ r_+, r_-, r_0 \ge 0}} \binom{n}{r_+}\binom{n - r_+}{r_0}(\alpha - 2)^{r_0}\binom{l - n}{r_-}(\alpha - 1)^{r_-}.$$

In particular, if $a$ is a current sequence at distance $n$ from an optimum $c$, the probability that a uniformly random sequence with exactly $r$ substitutions from $a$ lies at distance $m$ from the optimum is this count divided by $|S(a,r)| = \binom{l}{r}(\alpha - 1)^r$.

## Expansion

A point $b$ at distance $r$ from $a$ is obtained by substituting $r$ letters of $a$. Classify each substituted position $i$: if $a_i \ne c_i$ and $b_i = c_i$ the substitution is *beneficial* (it reduces the distance to $c$); if $a_i = c_i$ then $b_i \ne c_i$ and it is *deleterious* (increases the distance), with $\alpha - 1$ choices of letter; if $a_i \ne c_i$ and $b_i \notin \{a_i, c_i\}$ it is *neutral* (distance unchanged), with $\alpha - 2$ choices. Choosing $r_+$ beneficial positions among the $n$ mismatches, $r_0$ neutral ones among the remaining $n - r_+$ mismatches and $r_-$ deleterious ones among the $l - n$ matches gives the summand, and the constraints say that $r$ substitutions are used and $d_H(b,c) = n - r_+ + r_- = m$. Summing over $m < n$ yields the probability that $r$ random substitutions improve a sequence whose fitness is a decreasing function of distance, from which the optimal number of substitutions $r^*(n)$ (and the corresponding mutation rate) is chosen; it decreases as the sequence approaches the optimum.

## Sources

- R. V. Belavkin, A. Channon, E. Aston, J. Aston, R. Krašovec, C. G. Knight, "Monotonicity of fitness landscapes and mutation rate control", *Journal of Mathematical Biology* (2016), Appendix 1 (Proposition 1, Eq. (9)) and the section on mutation rate control in the geometric case, <https://doi.org/10.1007/s00285-016-0995-3> (PMC5061859).
