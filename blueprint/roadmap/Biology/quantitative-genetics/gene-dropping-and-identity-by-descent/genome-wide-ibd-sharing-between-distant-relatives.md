# Genome-wide IBD sharing between distant relatives

Let two relatives descend from a single common ancestor through a total of $2m$ meioses ($m$ on each side), and model crossovers in every meiosis as a Poisson process of rate $1$ per Morgan (no interference), independently across meioses. Let $I(x)$ be the indicator that the two relatives share DNA identical by descent (IBD) from this ancestor at genome position $x$, and let the autosomal genome have total map length $L$ Morgans.

1. **Pointwise probability.** $\Pr(I(x) = 1) = \beta = 2 \cdot 2^{-2m} = 2^{-(2m-1)}$.
2. **Segment lengths.** Along the genome, IBD segments from this ancestor have lengths approximately exponential with rate $2m$ (mean $1/(2m)$ Morgans); the segment covering a fixed IBD point is size-biased, the sum of two independent such exponentials (mean $1/m$ Morgans), ignoring chromosome ends.
3. **Probability of any sharing.** The number of shared segments is approximately Poisson, and the probability that the relatives share any IBD segment from the ancestor is approximately $1 - \exp\!\big(-(2m - 1) L \beta\big)$, which stays appreciable long after $\beta$ is negligible. For $12$ meioses $\beta \approx 0.0005$, yet the probability of sharing some autosomal segment is about $0.148$.
4. **Variance of the shared proportion.** The proportion $\frac1L \int_0^L I(x)\,dx$ has mean $\beta$ (or, in general, the kinship-based pointwise IBD probability $\psi$) and variance

$$\frac{1}{L^2}\int_0^L\!\!\int_0^L \Pr\big(I(x) = I(y) = 1\big)\,dx\,dy - \psi^2,$$

which depends only on two-locus IBD probabilities, i.e. on the recombination fraction between $x$ and $y$ and the pedigree.

At the population level, for a randomly mating population with effective sizes $N_e(s)$ at time depth $s$, the pointwise probability that two gametes are IBD relative to a reference time $t$ generations ago is

$$\beta(t) = 1 - \prod_{s=1}^{t}\left(1 - \frac{1}{2 N_e(s)}\right),$$

which increases with $t$ while the segments get shorter, so deeper reference times mean many more, shorter segments.

## Proof sketch

Item 1: each relative receives a given one of the ancestor's two genes with probability $2^{-m}$, independently, and either gene can be shared. Item 2: moving away from an IBD point, sharing is broken by the first crossover in any of the $2m$ meioses, a Poisson process of rate $2m$, so the distance to the segment end is $\mathrm{Exp}(2m)$ on each side; conditioning on covering a point size-biases the length (Cox's inspection paradox). Item 3 uses the Poisson approximation for rare, short segments (Donnelly 1983); a second-order effect is clumping, since a later crossover can restore IBD with probability of order $1/m$, and the Poisson clumping heuristic and exact methods refine the approximation. Item 4 is the second moment of an integral of indicators (Guo 1995). The product formula for $\beta(t)$ follows because two lineages fail to coalesce in generation $s$ with probability $1 - 1/(2N_e(s))$ under Wright–Fisher sampling. Thompson's review also stresses the large variance of segment length for a given number of meioses: for a $2$ cM segment the number of separating meioses has median about $35$ but ranges from about $6$ to $115$ between the $10\%$ and $90\%$ points.

## Depends on

- [Kinship in the gene-dropping model](ibd-model-kinship.md)
- [Haldane's map function](../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)

## Sources

- E. A. Thompson, "Identity by descent: variation in meiosis, across genomes, and in populations", Genetics 194 (2013), 301–326, section "The IBD process in a genome continuum" (variance formula, sharing probabilities, Equation 2), <https://doi.org/10.1534/genetics.112.148825> (PMC3664843).
