# Consistency of the linkage-disequilibrium estimator of effective population size under a calibration hypothesis

Let $K\ge1$ index a design of $K$ pairs of biallelic loci, the $k$-th pair having a known recombination fraction $c_{K,k}\in(0,\tfrac12]$, and let $\omega_{K,k}\ge0$ be fixed weights with $\sum_{k=1}^K\omega_{K,k}=1$. From a sample of size $n$, let $\hat r^2_k$ be the sample squared correlation of allelic states for pair $k$ and put

$$\hat m_K=\sum_{k=1}^K\omega_{K,k}\,\hat r^2_k .$$

A calibration family $m(N;c,n)$ is given in advance; for each $(c,n)$ the map $N\mapsto m(N;c,n)$ is continuous and strictly decreasing on $(0,\infty)$. The design calibration

$$m_K(N)=\sum_{k=1}^K\omega_{K,k}\,m(N;c_{K,k},n)$$

is then continuous and strictly decreasing on $(0,\infty)$. The estimator $\hat N_K\in[0,\infty]$ is

$$\hat N_K=\begin{cases}m_K^{-1}(\hat m_K), & \inf m_K<\hat m_K<\sup m_K,\\ 0, & \hat m_K\ge\sup m_K,\\ +\infty, & \hat m_K\le\inf m_K,\end{cases}$$

with $\inf$ and $\sup$ taken over $(0,\infty)$. Let $N_0\in(0,\infty)$ and assume, as $K\to\infty$:

- (S1) $m_K\to m_\infty$ uniformly on compact subsets of $(0,\infty)$;
- (S2) $m_\infty$ is continuous and strictly decreasing on $(0,\infty)$;
- (S3) $\hat m_K-m_K(N_0)\to0$ in probability.

Then $\hat N_K\to N_0$ in probability.

Two designs satisfy (S1) and (S2). (a) Common recombination fraction: if $c_{K,k}=c$ for all $K,k$, then $m_K=m(\,\cdot\,;c,n)$ does not depend on $K$, and (S1), (S2) hold with $m_\infty=m(\,\cdot\,;c,n)$. (b) Converging design law: if the design measures $G_K=\sum_k\omega_{K,k}\delta_{c_{K,k}}$ converge weakly on $(0,\tfrac12]$ to a probability measure $G$, and for each $N$ the map $c\mapsto m(N;c,n)$ is bounded and continuous, then $m_K(N)\to m_\infty(N)=\int m(N;c,n)\,G(dc)$ for every $N$. Then $m_\infty$ is strictly decreasing, and continuous by dominated convergence (for $N'$ near $N$, $m(N';c,n)$ lies between $m(2N;c,n)$ and $m(N/2;c,n)$, both bounded in $c$), so (S2) holds; pointwise convergence of the monotone functions $m_K$ to the continuous limit is uniform on compact sets, so (S1) holds. A design whose mixture of recombination fractions has no weak limit is not covered.

For the idealized common-$c$ calibration $m(N;c)=1/(1+4Nc)$, $c>0$ (an illustration, not a statement about $\mathbb E[r^2]$ in any population model), $m$ maps $(0,\infty)$ onto $(0,1)$ and

$$\hat N=\frac{1/\hat m-1}{4c}\quad(0<\hat m<1),\qquad \hat N=0\ (\hat m\ge1),\qquad \hat N=+\infty\ (\hat m\le0),$$

so $\hat N\to+\infty$ as $\hat m\downarrow0$. For a heterogeneous design no such closed form need exist: with $c=(0.01,\,0.5)$ and equal weights, $m_K(N)=\tfrac12\bigl[1/(1+0.04N)+1/(1+2N)\bigr]$. The quantity $\sigma_d^2$ of the [two-locus Wright–Fisher diffusion](../../coalescent-theory/two-locus-coalescent/two-locus-generator.md) is a ratio of expectations and is not $\mathbb E[r^2]$; no relation $\mathbb E[r^2]=1/(1+4Nc)$ is asserted. The interpretation of $N_0$ as the effective size of a closed, randomly mating population of constant size follows the [effective-size definitions](effective-population-size-definitions.md); selection, structure, admixture and changing size are outside the statement. The population-level relation between linkage disequilibrium and $N$, and the finite-sample bias of $\hat r^2$, are inputs (S3), not consequences.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)

## Proof depends on

- [Classical form of the recombination recursion](../linkage-disequilibrium-and-haldane-s-map-functio/recombine-eq-sub.md)
- [Prokhorov's theorem, sequential form on $\mathbb{R}$](../../../Probability/convergence-of-measures/prokhorov-theorem/prokhorov-sequential.md)

## Expansion

A full proof page must establish:

- The sequence theorem: for $0<\varepsilon<N_0$ put $\delta=\min\{m_\infty(N_0-\varepsilon)-m_\infty(N_0),\,m_\infty(N_0)-m_\infty(N_0+\varepsilon)\}>0$. Eventually $\sup_{[N_0-\varepsilon,N_0+\varepsilon]}|m_K-m_\infty|<\delta/3$, and with probability tending to one $|\hat m_K-m_K(N_0)|<\delta/3$; then $m_K(N_0+\varepsilon)<\hat m_K<m_K(N_0-\varepsilon)$, so $\hat N_K\in(N_0-\varepsilon,N_0+\varepsilon)$ by continuity and strict monotonicity of $m_K$.
- Case (b): weak convergence gives pointwise convergence of $m_K$; strict monotonicity and continuity of $m_\infty$; the Pólya-type lemma that pointwise convergence of monotone functions to a continuous limit is uniform on compact sets.
- The common-$c$ inversion formula and its boundary conventions.
- The two-point design $c=(0.01,0.5)$: $m_K(100)=\tfrac12(1/5+1/201)\approx0.10249$, while $(1/0.10249-1)/0.04\approx218.9\ne100$, so no single-$c$ inversion formula applies.
- With population $r^2=0$ and positive finite-sample $\mathbb E\,\hat r^2$, the idealized map returns a finite $\hat N$ (downward bias), so a sampling term in the calibration is necessary.

## Sources

- W. G. Hill, *Estimation of effective population size from data on linkage disequilibrium*, Genetical Research (1981), <https://core-varnish-new.prod.aop.cambridge.org/core/services/aop-cambridge-core/content/view/AA65A3B2E03EB5590444B886935D325E/S0016672300020553a.pdf/estimation_of_effective_population_size_from_data_on_linkage_disequilibrium1.pdf>, Summary and Sec. 2(i)–(ii): the variance of $r$ approximated as a ratio of moments with a population part in $(N,c)$ and a sampling part in $n$; $N$ estimated by replacing $\mathbb E(r^2)$ with its observed value and inverting.
- J. A. Sved, *Linkage disequilibrium and homozygosity of chromosome segments in finite populations* (1971), <https://pubmed.ncbi.nlm.nih.gov/5170716/> (population-level relation between linkage disequilibrium and $N$; background).
- R. S. Waples, *A bias correction for estimates of effective population size based on linkage disequilibrium at unlinked gene loci* (2006), <https://digitalcommons.unl.edu/usdeptcommercepub/441>, abstract: estimates from $\hat r^2$ at unlinked loci are biased downward when the sample size is below $N_e$.
- T. Ohta and M. Kimura, *Linkage disequilibrium due to random genetic drift* (1969), <https://resolve.cambridge.org/core/services/aop-cambridge-core/content/view/F2C75DE0F2B08F5BED09722614D0CD06/S001667230000272Xa.pdf/linkage_disequilibrium_due_to_random_genetic_drift.pdf> ($\sigma_d^2$ as a ratio of expectations, distinct from $\mathbb E[r^2]$).
