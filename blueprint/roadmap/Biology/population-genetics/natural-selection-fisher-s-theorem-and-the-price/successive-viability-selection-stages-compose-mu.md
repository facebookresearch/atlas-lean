# Successive viability selection stages compose multiplicatively

Let $I$ be a finite set of unchanged types, $x_i\ge0$ with $\sum_i x_i=1$, and
$w^{(1)},\ldots,w^{(s)}:I\to[0,\infty)$ fixed fitness vectors. Each stage is the
[selection map](select.md) $S_w(x)_i=x_iw_i/\sum_jx_jw_j$, with no mating,
mutation, migration or sampling between these stages. Assume
$\sum_i x_i\prod_{a=1}^s w_i^{(a)}>0$. Every partial selection is then defined
and remains in the frequency simplex, in any order, and

$$S_{w^{(s)}}\circ\cdots\circ S_{w^{(1)}}(x)
 = S_{\prod_{a=1}^s w^{(a)}}(x).$$

Thus these fixed selection stages commute. The assertion does not cover
frequency-dependent fitnesses or a change of genotype between stages.

For a diploid biallelic population, apply these stages to genotypes after
random union of gametes and before reproduction, and repeat the same cycle
every generation. If the three product fitnesses $W_{AA},W_{Aa},W_{aa}$ are
positive, the two rare-allele invasion multipliers are $W_{Aa}/W_{aa}$ and
$W_{Aa}/W_{AA}$. Both exceed one exactly when
$W_{Aa}>\max(W_{AA},W_{aa})$: protected polymorphism in this strict invasion
sense requires and is supplied by product-fitness overdominance. The stage
viabilities $0.8:0.9:1$ and $1:0.915:0.82$ give the products
$0.8:0.8235:0.82$, although neither stage is overdominant.
For two haploid types with positive product fitnesses $a,b$, the invasion
multipliers $a/b,b/a$ cannot both exceed one. Equal products instead give
neutral persistence of every initial frequency over a complete cycle; for
example stages $(1,1/2)$ and $(1/2,1)$ do this. Neutral polymorphism is not
excluded.

The order of different kinds of life-cycle stages need not be immaterial.
For example, mixing proportions $1-m,m$ of two Hardy-Weinberg adult
populations with allele frequencies $p_1,p_2\in[0,1]$, where $m\in[0,1]$,
gives $\bar p=(1-m)p_1+mp_2$ and heterozygosity

$$H_{\rm adults}=2\bar p(1-\bar p)-2m(1-m)(p_1-p_2)^2.$$

Pooling the corresponding gametes and then taking independent random unions
gives $H_{\rm gametes}=2\bar p(1-\bar p)$. The deficit is strictly positive
only when $0<m<1$ and $p_1\ne p_2$; adult migration does not invariably break
Hardy-Weinberg proportions.

## Depends on

- [Selection map](select.md)

## Expansion

For two stages, cancel the first normalization to obtain
$S_v(S_w(x))_i=x_iw_iv_i/\sum_jx_jw_jv_j$; induction proves the finite-stage
identity. Positive final mean implies a type with positive initial frequency
and all stage fitnesses positive, so all intermediate means in every order
are positive. Nonnegativity and normalization give closure. The diploid
multipliers follow by expanding the random-mating selection recursion at
$p=0,1$; the adult-mixture identity follows by expanding the three genotype
frequencies. Mutation, fertility, migration and sampling compositions, and
their equilibrium comparisons, remain separate contracts rather than
consequences of commutativity of diagonal selection.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, II.11, p. 116 (product fitnesses and overdominance); III.5, p. 147 (an explicitly ordered life cycle); IV.3, pp. 174–175 (adult mixtures and the Wahlund effect). The neutral exception and precise mixture conditions are explicit in the formulation above.
