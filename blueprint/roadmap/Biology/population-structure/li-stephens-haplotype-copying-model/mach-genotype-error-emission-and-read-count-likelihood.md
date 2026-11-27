# MaCH mosaic model: per-marker crossover and error parameters, genotype emissions and read-count likelihood

Let $H\ge1$ template haplotypes be typed at loci $j=1,\ldots,L$, with $T_j(i)\in\{0,1\}$ the allele of template $i$ at locus $j$ (coded as a count of one fixed allele). The hidden mosaic state of a diploid individual at locus $j$ is an ordered pair $S_j=(x_j,y_j)\in\{1,\ldots,H\}^2$: the first chromosome copies template $x_j$ and the second copies template $y_j$. The implied genotype is $T(S_j)=T_j(x_j)+T_j(y_j)\in\{0,1,2\}$. With a uniform initial law $P(S_1)$, the joint law of the observed genotypes $G=(G_1,\ldots,G_L)$ and the mosaic is

$$P(G,S)=P(S_1)\prod_{j=2}^{L}P(S_j\mid S_{j-1})\prod_{j=1}^{L}P(G_j\mid S_j).$$

**Transitions.** For a crossover parameter $\theta_j\in[0,1]$ of the interval between loci $j-1$ and $j$,

$$P(S_j\mid S_{j-1})=\begin{cases}\theta_j^2/H^2 & x_j\ne x_{j-1}\text{ and }y_j\ne y_{j-1},\\ (1-\theta_j)\theta_j/H+\theta_j^2/H^2 & \text{exactly one of }x_j\ne x_{j-1},\ y_j\ne y_{j-1},\\ (1-\theta_j)^2+2(1-\theta_j)\theta_j/H+\theta_j^2/H^2 & x_j=x_{j-1}\text{ and }y_j=y_{j-1}.\end{cases}$$

This is exactly $\tau_{\theta_j}(x_{j-1},x_j)\,\tau_{\theta_j}(y_{j-1},y_j)$ with the haploid copying kernel $\tau_\theta(k,k')=(1-\theta)[k=k']+\theta/H$, so the two chromosomes follow independent Li–Stephens copying chains with an interval-specific switch rate.

**Genotype emissions.** For an error parameter $\varepsilon_j\in[0,1]$ of marker $j$,

$$P(G_j\mid S_j)=\begin{cases}(1-\varepsilon_j)^2+\varepsilon_j^2 & T(S_j)=G_j,\ G_j\text{ heterozygous},\\ 2(1-\varepsilon_j)\varepsilon_j & T(S_j)\ne G_j,\ G_j\text{ heterozygous},\\ (1-\varepsilon_j)^2 & T(S_j)=G_j,\ G_j\text{ homozygous},\\ (1-\varepsilon_j)\varepsilon_j & T(S_j)\text{ heterozygous},\ G_j\text{ homozygous},\\ \varepsilon_j^2 & T(S_j),\ G_j\text{ opposite homozygotes}.\end{cases}$$

This is the law of $A'+B'$, where $A'$ and $B'$ are obtained from the two copied template alleles $T_j(x_j)$ and $T_j(y_j)$ by flipping each independently with probability $\varepsilon_j$. Consequently, for every state the five cases define a probability distribution on $G_j\in\{0,1,2\}$, and $P(G_j\mid S_j)$ depends on $S_j$ only through $T(S_j)$.

**Read counts.** When genotypes are not observed and the data at site $j$ are counts $A_j$, $B_j$ of reads showing alleles $A$ and $B$, with the read depths $d_j=A_j+B_j$ taken as given, the model becomes the likelihood conditional on the observed depths $d=(d_1,\ldots,d_L)$,

$$P(A,B,S\mid d)=P(S_1)\prod_{j=2}^{L}P(S_j\mid S_{j-1})\prod_{j=1}^{L}\sum_{G_j}P(G_j\mid S_j)\,P(A_j,B_j\mid G_j,d_j),$$

where, for a per-base sequencing error rate $\delta\in[0,1]$, $P(A_j,B_j\mid G_j,d_j)$ is the binomial probability of $A_j$ successes in $d_j$ trials with success probability $1-\delta$, $1/2$ or $\delta$ for $G_j=A/A$, $A/B$ or $B/B$ respectively. For each fixed depth $d_j$ these probabilities sum to $1$ over $A_j\in\{0,\ldots,d_j\}$; summed over both counts with the depth left free they do not, so a probability law for $(A_j,B_j)$ jointly would also need a law for the depths.

## Depends on

- [Li–Stephens copying transition probability](trans.md)
- [Li–Stephens emission probability](emit.md)
- [Diploid Li–Stephens model: collapsed forward step and imputed dosage as a posterior mean](diploid-li-stephens-phasing-and-genotype-imputat.md)

## Proof depends on

None beyond multiplying out the haploid kernels and enumerating independent allele flips, as the Expansion describes.

## Expansion

- Multiply out $\tau_\theta(x,x')\tau_\theta(y,y')$ in the three cases (no, one, or two switches) to recover the transition table; because the transition is a product of haploid kernels, the forward step collapses to $O(H^2)$ operations per locus through the row sums $C(a)$ and total $C$ of the weighted forward vector, as in the diploid Li–Stephens collapse.
- For the emissions, enumerate the flips: a true homozygote is read as the same homozygote with probability $(1-\varepsilon)^2$, as a heterozygote with $2\varepsilon(1-\varepsilon)$, and as the opposite homozygote with $\varepsilon^2$; a true heterozygote stays heterozygous when neither or both alleles flip, $(1-\varepsilon)^2+\varepsilon^2$, and becomes each homozygote with probability $\varepsilon(1-\varepsilon)$. Each row sums to $1$.
- The read-count model replaces the genotype emission by a mixture over latent genotypes, so the forward and backward recursions are unchanged with $P(G_j\mid S_j)$ replaced by $\sum_{G_j}P(G_j\mid S_j)P(A_j,B_j\mid G_j,d_j)$.
- In MaCH the $\theta_j$ and $\varepsilon_j$ are re-estimated at each iteration from the numbers of sampled mosaic change points and genotype mismatches, with pooling over intervals or markers having few events so that no parameter is set to zero.

## Sources

- Y. Li, C. J. Willer, J. Ding, P. Scheet, G. R. Abecasis, *MaCH: using sequence and genotype data to estimate haplotypes and unobserved genotypes*, Genetic Epidemiology 34 (2010), 816–834, <https://doi.org/10.1002/gepi.20533>, PMCID PMC3175618 (Appendix: Hidden Markov model, Parameter estimation, HMM for shotgun sequence data, Computational efficiency).
