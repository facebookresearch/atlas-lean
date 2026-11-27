# Real-rank Lindsey lemma

Let $B$ be a matrix over $\mathbb{F}_2$ with $\alpha$ rows and $\beta$ columns and let $M$ be any real matrix indexed by $\mathbb{F}_2^{\alpha}\times\mathbb{F}_2^{\beta}$. Then

$$
\Bigl(\sum_{p,q}M_{pq}(-1)^{p^{T}Bq}\Bigr)^2\cdot2^{\operatorname{rank}B}\le\operatorname{rank}(M)\cdot2^{\alpha+\beta}\sum_{p,q}M_{pq}^2 .
$$

For $M$ the indicator matrix of a rectangle this recovers Lindsey's lemma; for $M$ a sign or communication matrix it bounds correlation with high-rank bilinear forms by the real rank of $M$.

## Proof sketch

The sum is $\langle M, H\rangle$ for $H = ((-1)^{p^{T}Bq})$, and $|\langle M, H\rangle| \le \|M\|_{\mathrm{tr}}\,\|H\|$. The proof of Lindsey's lemma gives $\|H\|^2 = 2^{\alpha+\beta-\operatorname{rank}B}$, and Cauchy–Schwarz over the $\operatorname{rank}M$ nonzero singular values gives $\|M\|_{\mathrm{tr}}^2 \le \operatorname{rank}(M)\sum_{p,q}M_{pq}^2$.

## Proof depends on

- [Lindsey's lemma over GF(2)](lindsey-lemma-over-gf2.md)

## Sources

- Stasys Jukna, "Extremal Combinatorics: With Applications in Computer Science", Springer, 2011.
- Samuel Fiorini, Serge Massar, Sebastian Pokutta et al., "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
