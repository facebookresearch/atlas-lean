# Structured-coalescent hidden Markov model for a local tree under selection

Fix a biallelic site obeying the infinite-sites assumption and a labeled local genealogy of $n$ sampled haplotypes, in which each branch is known to carry the derived or the ancestral allele. Discretize time (in generations before the present) at $0 = t_0 < t_1 < \dots < t_K$, assume all lineages have coalesced by $t_K$, and let the derived-allele frequency $X_i$ and the (diploid) population size $N_i$ be constant on epoch $(t_i, t_{i+1}]$. Let $i^* = \max\{i : X_i > 0\}$ be the epoch in which the derived allele arose. Track the numbers of lineages at the epoch boundaries: $C^{\mathrm{der}}_i$ and $C^{\mathrm{anc}}_i$ within the derived and ancestral classes for $i \le i^*$, and $C^{\mathrm{mix}}_i$ for the merged population older than the mutation.

**Model.** Lineages coalesce only within their allelic class, as in a population of size $z$ equal to the size of that class:

$$z_i^{\mathrm{der}} = N_i X_i, \qquad z_i^{\mathrm{anc}} = N_i(1 - X_i), \qquad z_i^{\mathrm{mix}} = N_i .$$

Given the trajectory $X = (X_i)$,

$$P(C \mid X, N) = \prod_{i=0}^{i^*-1} P\bigl(C^{\mathrm{der}}_{i+1} \mid C^{\mathrm{der}}_i, z_i^{\mathrm{der}}\bigr)\,P\bigl(C^{\mathrm{anc}}_{i+1} \mid C^{\mathrm{anc}}_i, z_i^{\mathrm{anc}}\bigr) \prod_{i=i^*}^{K-1} P\bigl(C^{\mathrm{mix}}_{i+1} \mid C^{\mathrm{mix}}_i, z_i^{\mathrm{mix}}\bigr),$$

where each factor is Tavaré's probability that $a$ lineages leave $b$ ancestors after coalescent time $\Delta\tau_i = (t_{i+1} - t_i)/(2z_i)$:

$$P(b \mid a, z) = \sum_{k=b}^{a} e^{-\binom k2 \Delta\tau}\, \frac{(2k-1)(-1)^{k-b}}{b!\,(k-b)!\,(k+b-1)} \prod_{l=0}^{k-1} \frac{(b+l)(a-l)}{a+l}.$$

If the trajectory is a Markov chain on $d$ frequency values whose transitions depend on the selection coefficient $s$ (a discretized Wright–Fisher model with additive selection), then

$$P(C \mid s) = \sum_{x} P(C \mid X = x)\,P(X = x \mid s)$$

is computable by forward and backward recursions that marginalize one epoch at a time, in $O(Kd^2)$ operations instead of a sum over $d^{K-1}$ trajectories, and the posterior marginal of the frequency in epoch $i$ is

$$P(X_i = x_i \mid C, s) = \frac{b_i(x_i) f_i(x_i)}{\sum_{x'} b_i(x') f_i(x')}$$

with $b_i$, $f_i$ the backward and forward messages.

## Remarks

Exchangeability within each allelic class means only the lineage counts, not the topology, enter the likelihood given the waiting times. The hidden layer is the trajectory; the "emissions" are the coalescence counts, which depend on the current frequency and on the current lineage numbers, so the chain is time-inhomogeneous but has the usual hidden-Markov dependence structure. At the mutation epoch the derived class has collapsed to a single lineage, which joins the ancestral class and makes $C^{\mathrm{mix}}$ exceed $C^{\mathrm{anc}}$ by one. For very large $z$ or short epochs the alternating series is numerically unstable and is replaced by its normal approximation. Sharp coalescence bursts in the derived class point to a recent rapid frequency rise, which is how the model extracts information on $s$ and on the trajectory.

## Depends on

- [Tavaré's formula for the number of ancestral lineages](../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)

## Sources

- A. J. Stern, P. R. Wilton and R. Nielsen, "An approximate full-likelihood method for inferring selection and allele frequency trajectories from DNA sequence data", PLoS Genetics 15 (2019), e1008384, Materials and methods, Equations (1)–(4), (9)–(10), <https://doi.org/10.1371/journal.pgen.1008384> (PMCID: PMC6760815).
