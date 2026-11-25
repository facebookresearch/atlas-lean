# Hudson F_ST need not add along a neutral lineage

Define $f_2(X,Y)=\mathbb E(p_X-p_Y)^2$ and, when its denominator is
positive, the population Hudson ratio
$F_{ST}(X,Y)=f_2(X,Y)/\pi_{XY}$, where
$\pi_{XY}=\mathbb E[p_X(1-p_Y)+p_Y(1-p_X)]$.
This is a ratio of expectations, not a mean of per-locus ratios or an
unqualified finite-sample estimator.

On a two-edge lineage with fixed $p_{\rm anc}=1/2$, one neutral generation
and $M=2$ copies on each edge,

$$f_2(\mathrm{anc},\mathrm{desc})=\tfrac3{16}
 =\tfrac18+\tfrac1{16}
 =f_2(\mathrm{anc},\mathrm{mid})+f_2(\mathrm{mid},\mathrm{desc}),$$

but $\pi_{\mathrm{anc},\mathrm{mid}}=\pi_{\mathrm{anc},\mathrm{desc}}=1/2$
and $\pi_{\mathrm{mid},\mathrm{desc}}=1/4$, so

$$F_{ST}(\mathrm{anc},\mathrm{desc})=\tfrac38
 \ne\tfrac14+\tfrac14
 =F_{ST}(\mathrm{anc},\mathrm{mid})+F_{ST}(\mathrm{mid},\mathrm{desc}).$$

## Depends on

- [Neutral lineage second moments](martingale-orthogonality-of-drift-increments-alo.md)

## Expansion

The middle frequency has probabilities $(1/4,1/2,1/4)$ on
$(0,1/2,1)$, so its expected heterozygosity is $1/4$ after starting at
$1/2$. The next generation halves it again. The lineage formula gives
edge second moments $1/8,1/16$ and total $3/16$.
The constant ancestral frequency makes each ancestral diversity denominator
$1/2$. Conditional neutrality gives
$\pi_{\mathrm{mid},\mathrm{desc}}
=2\mathbb E[p_{\rm mid}(1-p_{\rm mid})]=1/4$.
All denominators are positive. The example refutes additivity of this
normalized index, not all metrics called fixation indices.

## Sources

- B. M. Peter, *Admixture, population structure, and F-statistics*, Genetics 202 (2016), 1485–1501, <https://doi.org/10.1534/genetics.115.183913>, bibliographic background only, not used as proof. The complete finite rational example is derived above.
