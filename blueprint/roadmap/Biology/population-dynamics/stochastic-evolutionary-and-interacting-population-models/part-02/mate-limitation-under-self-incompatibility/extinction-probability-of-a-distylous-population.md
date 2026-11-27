# Extinction probability of a distylous self-incompatible population

**Model.** Diploid hermaphroditic plants carry an S-locus genotype in $\{1,1\}$, $\{1,2\}$, $\{2,2\}$; under distyly allele $2$ is dominant and $1$ recessive in both pollen and stigma, so a cross is compatible iff the two parents express different phenotypes. (If the two alleles were codominant, heterozygotes would have no compatible mate and the population would go extinct almost surely after at most two generations.) Starting from genotypes $\{1,1\}$ and $\{1,2\}$ only, $\{2,2\}$ never arises, and the counts $(N^{11}_t, N^{12}_t)$ form a continuous-time Markov chain: every plant dies at rate $d > 0$, and in *Wright's model* (no pollen limitation) every plant produces ovules at rate $\bar r$, each fertilized by pollen of a uniformly chosen plant of the other genotype as long as one exists; an offspring of a $\{1,1\}\times\{1,2\}$ cross is $\{1,1\}$ or $\{1,2\}$ with probability $\tfrac12$ each. The population is doomed once either genotype disappears; let $p_{i,j}$ be the probability that this happens, starting from $(N^{11}_0, N^{12}_0) = (i,j)$ with $i, j \ge 1$.

**Theorem.**

1. The extinction probabilities satisfy, for $i, j \ge 1$,

$$ p_{i,j} = \frac{d\,i}{(\bar r + d)(i+j)}\,p_{i-1,j} + \frac{d\,j}{(\bar r + d)(i+j)}\,p_{i,j-1} + \frac{\bar r}{2(\bar r + d)}\,p_{i,j+1} + \frac{\bar r}{2(\bar r + d)}\,p_{i+1,j}, $$

   with $p_{0,j} = p_{i,0} = 1$, and $(p_{i,j})$ is the minimal nonnegative solution of this Dirichlet problem.
2. Extinction in finite time is almost sure iff $\bar r \le d$.
3. If $\bar r > d$, the survival probability $1 - p_{i,j}$ is positive and

$$ \Big(\frac{d}{\bar r}\Big)^{i+j} \le p_{i,j} \le \Big(\frac{d}{\bar r}\Big)^{i} + \Big(\frac{d}{\bar r}\Big)^{j} - \Big(\frac{d}{\bar r}\Big)^{i+j}. $$

4. In the *fecundity-selection model*, where an ovule is fertilized with probability equal to the frequency of compatible plants, extinction is almost sure iff $\bar r \le 2d$, and for $\bar r > 2d$ one has $(d/\bar r)^{i+j} \le p_{i,j} \le (2d/\bar r)^{\min(i,j)}$.

In the large-population limit of Wright's model, the rescaled densities solve $\dot n = (\tfrac{\bar r}{2}J - dI)n$ with $J$ the all-ones $2\times2$ matrix, so both types grow like $e^{(\bar r - d)t}$ and approach equal frequencies; mate limitation thus shows up only through the boundary of the quadrant, i.e. in small populations.

## Expansion

The recursion is first-step analysis: from $(i,j)$ the next event is a death of a $\{1,1\}$ plant (rate $di$), a death of a $\{1,2\}$ plant (rate $dj$), or a birth (total rate $\bar r(i+j)$), whose offspring type is a fair coin. The total size $N = N^{11} + N^{12}$ is a linear birth–death process with rates $\bar r$ and $d$ until the boundary is hit, which gives the lower bound $(d/\bar r)^{i+j}$, the extinction probability of $N$ itself. For the upper bound, couple with a process in which the two genotypes evolve as independent linear birth–death processes with birth rate $\bar r$ and death rate $d$; it leaves the open quadrant with probability exactly $(d/\bar r)^i + (d/\bar r)^j - (d/\bar r)^{i+j}$, and the coupling makes the original process at least as likely to survive. In the fecundity-selection model the effective birth rate per plant is halved at balanced frequencies, which explains the threshold $2d$.

## Sources

- Sylvain Billiard, Viet Chi Tran, "A general stochastic model for sporophytic self-incompatibility", arXiv:1010.2984 (2010), Section 2.1–2.2 (individual-based model, Wright's model), Section 2.4 (Proposition 2.3, distylous random walk), Section 3.1 (Proposition 3.1), Section 3.3 (Proposition 3.8), Section 4.1 (Propositions 4.1–4.5), Section 4.2 (Proposition 4.6). <https://doi.org/10.48550/arXiv.1010.2984>. Published version: Journal of Mathematical Biology 64(1-2) (2012), 163–210, <https://doi.org/10.1007/s00285-011-0410-z>; locators above refer to the arXiv version.
