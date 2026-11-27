# Background selection and recurrent sweeps in the coalescent

Background selection reduces diversity at neutral sites linked to sites under purifying selection, because a new neutral variant can persist only on chromosomes free of deleterious alleles (Charlesworth, Morgan and Charlesworth 1993). At a constrained locus with mutation rate $\mu$ to deleterious alleles of heterozygous selection coefficient $sh$, the deleterious allele has equilibrium frequency approximately $\mu/(sh)$ at mutation–selection balance (Crow and Kimura 1970, Ch. 6; Nordborg, Charlesworth and Charlesworth 1996); a completely linked neutral locus therefore has only $2N(1 - \mu/(sh))$ chromosomes that contribute to future generations, giving $E[\pi] = \pi_0(1 - \mu/(sh))$, with $\pi_0 = 4N\mu_n$ the diversity without linked selection for a neutral mutation rate $\mu_n$.

Recurrent selective sweeps can change the form of the genealogy. Durrett and Schweinsberg (2005, Theorem 2.2) consider a Moran population of size $2N$ whose chromosome is the segment $[-L, L]$, in which beneficial mutations with selective advantage $s \in [0, 1]$ arise at position $x \in [-L, L]$ according to a Poisson process on $\mathbb R \times [-L, L] \times [0, 1]$ with intensity $\lambda \times \mu_N$, for $\lambda$ Lebesgue measure and $\mu_N$ a finite measure on $[-L, L] \times [0, 1]$, and the recombination probability between position $x$ and the sampled site $0$ is $r_N(x)$, where $r_N : [-L, L] \to [0, 1]$ has $r_N(0) = 0$ and is nonincreasing on $[-L, 0]$ and nondecreasing on $[0, L]$; a point of the Poisson process produces a beneficial mutation only when no other beneficial mutation is present in the population, and points arriving during a sweep are discarded (Section 2.2). Let $\mu$ be a finite measure on $[-L, L] \times [0, 1]$ and let $r : [-L, L] \to [0, \infty)$ be a bounded continuous function with $r(0) = 0$ that is nonincreasing on $[-L, 0]$ and nondecreasing on $[0, L]$. If $N\mu_N \to \mu$ weakly and $(\log 2N)r_N \to r$ uniformly, then the ancestral partition of a sample, with time sped up by $N$, converges in finite-dimensional distributions to the [$\Lambda$-coalescent](../../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md) with $\Lambda = \delta_0 + x^2\eta(dx)$, where $\eta$ is the measure on $(0, 1]$ with $\eta([y, 1]) = \int s\,\mathbf 1\{e^{-r(x)/s} \ge y\}\,\mu(dx \times ds)$ for $y \in (0, 1]$; convergence in the Skorokhod topology fails because several transitions occur during each short sweep. Sweeps thus add multiple mergers on the same time scale as Kingman's binary mergers, while a rate of sweeps of smaller order makes the multiple mergers disappear in the limit. Reduction of the effective size to the mutation-free class in a non-recombining genome under multiplicative mutation–selection balance is a separate statement.

## Depends on

- [The Λ-coalescent on the natural numbers](../../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
- [Pitman's merger rate](../../coalescents/merger-rate.md)

## Expansion

1. Mutation–selection balance at a constrained locus and the fraction of chromosomes free of the deleterious allele.
2. The reduction of neutral diversity for complete linkage; the effect of a partly linked constrained locus at recombination fraction $c$ (Hudson and Kaplan 1995; Nordborg, Charlesworth and Charlesworth 1996), as a separate statement.
3. The Moran model with recurrent beneficial mutations, the scaling of the mutation rate and of the recombination probabilities, and the limiting measure $\Lambda = \delta_0 + x^2\eta(dx)$ (Theorem 2.2).
4. The single-site example with fixed $s$, and the finite-population approximation by a coalescent with simultaneous multiple mergers.
5. Criteria separating a time change of Kingman's coalescent (background selection) from a multiple-merger limit (recurrent sweeps), and the consequences for the site-frequency spectrum.

## Sources

- B. Charlesworth, M. T. Morgan and D. Charlesworth, The effect of deleterious mutations on neutral molecular variation, Genetics 134 (1993), 1289–1303. <https://doi.org/10.1093/genetics/134.4.1289>
- M. Nordborg, B. Charlesworth and D. Charlesworth, The effect of recombination on background selection, Genet. Res. 67 (1996), 159–174. <https://doi.org/10.1017/S0016672300033619>
- R. R. Hudson and N. L. Kaplan, Deleterious background selection with recombination, Genetics 141 (1995), 1605–1617. <https://doi.org/10.1093/genetics/141.4.1605>
- J. F. Crow and M. Kimura, *An Introduction to Population Genetics Theory*, Harper & Row, 1970, Ch. 6.
- R. Durrett and J. Schweinsberg, A coalescent model for the effect of advantageous mutations on the genealogy of a population, Stochastic Process. Appl. 115 (2005), 1628–1657, Sections 2.2–2.3 and Theorem 2.2. <https://arxiv.org/abs/math/0411071>
