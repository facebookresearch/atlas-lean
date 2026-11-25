# Allele-frequency change under a specified gene-conversion transmission bias

Let a finite set of alleles have frequencies $p_i\ge0$, $\sum_i p_i=1$.
Use a deterministic diploid, random-mating model with discrete generations,
no mutation, no viability differences and no drift. Homozygotes transmit
their allele. For each heterozygote $ij$, let the probability of transmitting
$i$ be $(1+b_{ij})/2$, where $b_{ii}=0$, $b_{ji}=-b_{ij}$ and
$|b_{ij}|\le1$. Both sexes use this rule. Then the next gamete frequencies are

$$p'_i=p_i^2+\sum_{j\ne i}p_ip_j(1+b_{ij})
       =p_i\left(1+\sum_j b_{ij}p_j\right).$$

They are nonnegative and sum to one. An absent allele remains absent.
For two alleles $A,a$ with $b_{Aa}=b\in[0,1]$, this is
$p'=p+bp(1-p)$. If $b>0$ and $p_0>0$, the deterministic frequency tends to
one by the [meiotic-drive result](../one-locus-selection-dynamics/meiotic-drive-without-viability-differences.md) with $k = (1 + b)/2$.
Here $b$ can be interpreted as the fraction of the gametes that otherwise
would carry $a$ in an $Aa$ heterozygote but carry $A$ after conversion.

This operator differs from two-way mutation, whose increment is
$v(1-p)-up$ for mutation probabilities $u:A\to a$, $v:a\to A$.
Mutation can introduce an absent allele. It also differs from haploid
viability selection with fitnesses $1+s,1$ ($s>0$), whose increment is
$sp(1-p)/(1+sp)$. Similar weak-effect approximations do not identify these
mechanisms or their life cycles.

No exception-free multiallelic extinction conclusion follows from bias in
every pair. For three alleles, take
$b_{12}=b_{23}=b_{31}=1/2$ and the opposite entries $-1/2$.
Every pair is biased, but $p=(1/3,1/3,1/3)$ is fixed, since every row sum is
zero. This is an exact counterexample in the stated deterministic model.

## Proof depends on

- [Allele frequency change under meiotic drive without viability differences](../one-locus-selection-dynamics/meiotic-drive-without-viability-differences.md)

## Expansion

Random union gives heterozygote frequency $2p_ip_j$; multiplying by its
transmission probability gives the recursion. Nonnegativity follows either
from this expression or from $\sum_jb_{ij}p_j\ge-1$. Normalization follows
from $\sum_{i,j}p_ib_{ij}p_j=0$ by antisymmetry. The cyclic example is checked
by substitution. Finite-population noise, generic initial conditions and
long-term multiallelic behavior require separately stated hypotheses and
results. No source-specific multiallelic extinction theorem is asserted here.

## Sources

- T. Nagylaki, "Evolution of a large population under gene conversion", PNAS 80 (1983), 5941–5945, <https://doi.org/10.1073/pnas.80.19.5941>, abstract. It says that analytical and numerical investigation "indicates" its multiallelic conclusions and discusses random perturbations. The explicit reduced transmission model and counterexample above are derived here; the abstract is not treated as an exception-free theorem for all initial states.
