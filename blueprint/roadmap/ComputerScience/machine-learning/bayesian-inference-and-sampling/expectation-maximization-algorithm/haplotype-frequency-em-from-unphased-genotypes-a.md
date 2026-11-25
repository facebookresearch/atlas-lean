# Haplotype-frequency EM from unphased genotypes

For $L\ge1$ biallelic loci let $h$ be a probability vector on
$\{0,1\}^L$. An unphased genotype $g\in\{0,1,2\}^L$ has compatible
ordered haplotype pairs $C(g)=\{(a,b):a+b=g\}$.
Under independent haplotype union, $P_h(g)=\sum_{(a,b)\in C(g)}h_a h_b$.
For a sample $g_1,\ldots,g_n$ with $n\ge1$ and $P_h(g_i)>0$, define

$$h'_a=\frac1{2n}\sum_{i=1}^n\sum_{(b,c)\in C(g_i)}
 \frac{h_bh_c}{P_h(g_i)}\bigl(\mathbf1_{b=a}+\mathbf1_{c=a}\bigr).$$

Then $h'$ is a probability vector, every observed genotype still has
positive probability, and $\sum_i\log P_{h'}(g_i)\ge\sum_i\log P_h(g_i)$.
If each genotype is heterozygous at at most one locus, one step returns
the actual counted haplotype frequencies.
The finite-sample likelihood can have strict nonglobal local maxima,
despite population identifiability.

## Background

- [Evidence lower bound](elbo-le-log-lik.md)
- [Population identification of two-locus haplotypes](../../../../Biology/population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/two-locus-haplotype-frequencies-are-identified-b.md)

## Expansion

The posterior phase weights sum to one for each observation, so the
expected chromosome counts sum to $2n$. Any old positive phase weight
assigns positive expected counts to both of its haplotypes. Thus its pair
probability under $h'$ is positive and every observed $P_{h'}(g_i)>0$.

The linked generic ELBO assumes positivity for every latent configuration;
this model has structural zeros and may have zero haplotype frequencies.
Instead restrict Jensen's inequality, for each observation, to the pairs
with positive old posterior weight. On that support,
$\log(P_{h'}(g_i)/P_h(g_i))$ is at least the posterior mean of
$\log(h'_b h'_c/(h_bh_c))$; omitted pairs only increase the new likelihood.
Summing gives the increase in the complete-data objective
$\sum_a r_a\log h_a$, where $r_a$ are the expected chromosome counts.
Its maximum on the simplex is attained at $h'_a=r_a/(2n)$, with zero
count terms read as zero. This proves monotonicity without an invalid
full-support premise. There is no prerequisite beyond the explicit finite
model and this support-restricted derivation.

For a concrete two-locus example, count genotypes by copies of the two
reference alleles: $(0,0):3$, $(0,2):1$, $(2,0):5$, $(2,1):3$, $(1,1):40$.
There are $52$ individuals. Write haplotypes in order $AB,Ab,aB,ab$.
Every EM update has the form
$H(t)=(3+40t,53-40t,42-40t,6+40t)/104$, where
$t=h_{AB}h_{ab}/(h_{AB}h_{ab}+h_{Ab}h_{aB})$.
At a fixed point,
$1600t^3-2520t^2+942t-9=0$.
This cubic has three roots in $(0,1)$, one each in
$(0.009,0.011)$, $(0.58,0.59)$ and $(0.98,0.99)$.
The first and third give respectively
$(0.0326192,0.5058423,0.4000731,0.0614654)$ and
$(0.4058575,0.1326040,0.0268348,0.4347037)$,
with log-likelihoods about $-71.4022253$ and $-79.9946435$.

The lower-likelihood point is a strict local maximum, not merely an
observed stopping point. In coordinates $h_4=1-h_1-h_2-h_3$, the three
leading principal minors of the likelihood Hessian there lie in
$(-496,-495)$, $(412093,412094)$ and
$(-1129731752,-1129731751)$, respectively.
These bounds follow by rational root isolation and interval evaluation
of the Hessian of
$3\log h_1+13\log h_2+2\log h_3+6\log h_4
+40\log(h_1h_4+h_2h_3)+43\log2$.
The tangent gradient is zero at the fixed point and Sylvester's criterion
makes the Hessian negative definite. Direct positive rational likelihood
bounds distinguish the two maxima, not just rounded log values.
The phase update is strictly increasing on $[0,1]$; the cubic's signs
show attraction to the first or third root on either side of the middle
root. The starts $(0.01,0.5,0.2,0.29)$ and $(0.45,0.1,0.05,0.4)$ have
phase values $29/1029$ and $36/37$ in the respective basins.

## Sources

- L. Excoffier and M. Slatkin, "Maximum-likelihood estimation of molecular haplotype frequencies in a diploid population", Molecular Biology and Evolution 12 (1995), 921–927, <https://doi.org/10.1093/oxfordjournals.molbev.a040269>. The example is computed above.
