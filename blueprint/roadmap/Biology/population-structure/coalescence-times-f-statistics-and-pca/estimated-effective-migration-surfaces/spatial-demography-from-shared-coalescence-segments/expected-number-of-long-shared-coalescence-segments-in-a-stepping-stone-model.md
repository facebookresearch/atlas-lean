# Expected number of long shared-coalescence segments in a stepping-stone model

Two haploid genomes $i$ and $j$ share a **pairwise shared coalescence (PSC) segment** wherever they have a single coalescence time along a contiguous stretch of genome. Let $G$ be the genome length in base pairs, $r$ the recombination rate per base pair per generation, $T_{ij}$ the coalescence time (in generations) of $i$ and $j$ at a fixed site with density $f_{T_{ij}}(t \mid \Theta)$ under demographic parameters $\Theta$, and $L$ the length of the PSC segment containing that site. Let $X^{[\mu,\infty)}_{ij}$ be the number of PSC segments of length at least $\mu$ base pairs shared by $i$ and $j$.

**Segment-length law.** Given $T_{ij} = t$, both ends of the segment are hit by recombination at total rate $2tr$ per base pair on each side, so $L$ is Erlang-2:

$$f_L(l \mid t) = 4r^2t^2\,l\,e^{-2trl}, \qquad l > 0,$$

independent of $\Theta$ given $t$.

**Expected count.** Neglecting edge effects of finite chromosomes,

$$\mathbb{E}\big[X^{[\mu,\infty)}_{ij} \mid \Theta\big] \approx G\int_\mu^\infty \frac{f_L(l \mid \Theta)}{l}\,dl = G\int_0^\infty f_{T_{ij}}(t \mid \Theta)\,2rt\,e^{-2tr\mu}\,dt,$$

and for a length bin $[\mu, \nu]$ the expected count is the difference of the two tail counts. With lengths in centimorgans, $\mu_{\mathrm{cM}} = 100\,\mu r$.

**Stepping-stone coalescence time.** On a grid of $d$ demes with symmetric migration-rate matrix $M$ and coalescence rate $q_\kappa = 1/(2N_\kappa)$ in deme $\kappa$, for $i$ sampled in deme $\alpha$ and $j$ in deme $\beta$, the coalescence-time density is approximated by

$$f_{T_{ij}}(t \mid \Theta) \approx \sum_{\kappa=1}^{d} q_\kappa\,\big(e^{-Mt}\big)_{\alpha\kappa}\big(e^{-Mt}\big)_{\beta\kappa},$$

computed by diagonalizing $M = PDP^{\top}$, $e^{-Mt} = Pe^{-Dt}P^{\top}$, after which the one-dimensional time integral is evaluated by Gaussian quadrature. The recombination map acts as an independent clock, so migration rates and population sizes are identified in absolute (not only effective) units.

## Proof sketch

The expected number of base pairs lying in PSC segments of length in $[l, l+dl]$ is $G f_L(l)\,dl$, because $f_L$ is the length law of the segment covering a fixed site (a length-biased law); dividing by $l$ converts covered base pairs into segment counts. Writing $f_L(l \mid \Theta) = \int_0^\infty f_L(l \mid t) f_{T_{ij}}(t \mid \Theta)\,dt$ and exchanging integrals, the inner integral is

$$\int_\mu^\infty \frac{4r^2t^2 l e^{-2trl}}{l}\,dl = 4r^2t^2\cdot\frac{e^{-2tr\mu}}{2tr} = 2rt\,e^{-2tr\mu}.$$

The Erlang-2 law is the length-biased version of the exponential($2tr$) length of a segment chosen uniformly among segments: the covering segment extends from the focal site to the first recombination on each side, two independent exponential distances. In the stepping-stone approximation, $(e^{-Mt})_{\alpha\kappa}$ is the probability that a lineage started in $\alpha$ is in deme $\kappa$ at time $t$, so the sum is the rate at which two independently migrating lineages are found together in a deme and coalesce; for recent times, the regime probed by long segments, prior coalescence is rare and this rate approximates the density.

## Depends on

- [Structured coalescent for n lineages with a general migration matrix](../../../../coalescent-theory/structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)

## Sources

- H. Al-Asadi, D. Petkova, M. Stephens and J. Novembre, "Estimating recent migration and population-size surfaces", *PLoS Genetics* 15 (2019), e1007908, Methods "Computing the expectation of $X^R_{i,j} \mid \Theta$", Equations (8)–(16), <https://doi.org/10.1371/journal.pgen.1007908> (PMC6347299).
