# Converting neutral lineage f2 to population-scaled generations

Consider a finite ancestor-to-descendant lineage without admixture,
mutation or selection. Edge $e$ has integer $t_e\ge0$ generations of
binomial drift with integer $M_e\ge2$ gene copies. Let
$H_0=2\mathbb E[p_{\rm anc}(1-p_{\rm anc})]>0$. Then

$$f_2(\mathrm{anc},\mathrm{desc})
 =\tfrac12H_0\left(1-\prod_e(1-1/M_e)^{t_e}\right)<H_0/2,$$

and the natural-log transform is exactly

$$-\log(1-2f_2/H_0)=\sum_e t_e[-\log(1-1/M_e)].$$

It is additive in size-adjusted generations. The elementary bounds give

$$\sum_e\frac{t_e}{M_e}
 \le-\log(1-2f_2/H_0)
 \le\sum_e\frac{t_e}{M_e-1}.$$

Thus the approximation by $\sum_e t_e/M_e$ is controlled when the copy
counts are large. A positive-length edge with $M_e=1$ fixes the allele,
gives $f_2=H_0/2$ and makes this logarithmic transform infinite.
A zero-step edge, even with $M_e=1$, does not do so.

## Depends on

- [Neutral lineage second moments and additivity](martingale-orthogonality-of-drift-increments-alo.md)

## Proof depends on

- [Wright–Fisher heterozygosity decay](../../population-genetics/wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)

## Expansion

Conditioning successively propagates expected heterozygosity by the product
of the edge retention factors. The lineage martingale identity expresses
$f_2$ as half the heterozygosity lost. Each factor is positive for finite
$t_e$ and $M_e\ge2$, proving strict inequality. Taking logarithms proves
additivity. Integrating $1/(1-x)$ between zero and $x\in(0,1)$ yields
$x\le-\log(1-x)\le x/(1-x)$ and the displayed bounds.
The untransformed $f_2$ is also exactly additive in the **unconditional
edge increment second moments**, by martingale orthogonality; those edge
values already account for decreasing ancestral heterozygosity. It is
not proportional to generations at one fixed rate for all depths.
No individual edge time can be recovered from the total alone without
its sizes and the other edge contributions.

## Sources

- S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and F-statistics* (2019), <https://doi.org/10.1016/j.tpb.2018.12.002>, <https://arxiv.org/abs/1807.07593>, equation (10), for the diffusion counterpart. The discrete product, endpoint and logarithmic bounds are derived above.
