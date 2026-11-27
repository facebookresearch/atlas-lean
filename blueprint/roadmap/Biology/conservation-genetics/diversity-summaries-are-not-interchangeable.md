# Heterozygosity, allelic richness and rare-allele retention are distinct summaries

On the fixed allele set $\{1,2,3\}$, let $p_i\ge0$ and $\sum_i p_i=1$.
Define $H(p)=1-\sum_i p_i^2$ and $A(p)=|\{i:p_i>0\}|$.
Fix the reference frequencies $p^{(0)}=(1/100,99/200,99/200)$, so allele
$1$ is initially rare. Define its retention at a later frequency vector by
$R(p)=\mathbf 1_{\{p_1>0\}}$. This is retention of a designated initially
rare allele, not a claim about which alleles are rare at the later time.

- $(1/2,1/2,0)$ and $(2/3,1/6,1/6)$ both have $H=1/2$, but have richness
  $2$ and $3$.
- $(1/2,1/2,0)$ and $(9/10,1/10,0)$ both have richness $2$, but have
  $H=1/2$ and $H=9/50$.
- $(1/2,1/2,0)$ and $(0,1/2,1/2)$ have the same heterozygosity and
  richness, but retention $1$ and $0$.
- $(1/2,1/2,0)$ and $(1/3,1/3,1/3)$ both retain allele $1$, but have
  different heterozygosities ($1/2,2/3$) and richnesses ($2,3$).

Thus none of these three scalar summaries determines either of the others.
All vectors, including the reference, can be represented with $600$ gene
copies, so these are also finite count examples. The result compares
summaries; it presupposes no particular dynamics connecting the snapshots.

## Expansion

Each assertion is direct substitution into the definitions. Sample richness,
sample heterozygosity and stochastic loss times need separate models. In
particular a statement that rare alleles are lost "faster" must specify the
initial states, the loss-time statistic and its comparison; it does not
follow from these finite examples or from geometric mean-heterozygosity decay.

## Sources

The finite examples and their verification are elementary calculations given
above; no external theorem is invoked.
