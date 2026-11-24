# Background selection and recurrent sweeps in the coalescent

Background selection reduces diversity at neutral sites linked to sites under purifying selection. In the account of Coop (Population and Quantitative Genetics, Chapter 13, Background selection), a constrained locus with mutation rate $\mu$ to deleterious alleles of heterozygous selection coefficient $sh$ carries the deleterious allele on a fraction $\mu/(sh)$ of chromosomes at mutation–selection balance; a completely linked neutral locus therefore has only $2N(1 - \mu/(sh))$ chromosomes that contribute to future generations, giving $E[\pi] = \pi_0(1 - \mu/(sh))$, with $\pi_0 = 4N\mu_n$ the diversity without linked selection for a neutral mutation rate $\mu_n$. For a neutral locus at recombination fraction $c$ from the constrained locus, Coop gives a separate approximation,

$$E[\pi] = \pi_0\Bigl(1 - \frac{\mu sh}{2(c + sh)^2}\Bigr),$$

in which the reduction decreases as $c$ grows. At $c = 0$ this second expression gives $1 - \mu/(2sh)$, half the reduction of the complete-linkage formula, so the two expressions rest on different conventions for the mutation rate (per gamete or per diploid) or on different approximations, and neither is a continuation of the other.

Recurrent selective sweeps can change the form of the genealogy. Durrett and Schweinsberg (2005, Theorem 2.2) consider a Moran population of size $2N$ in which beneficial mutations with selective advantage $s$ arise at chromosome position $x$ at the times of a Poisson process with intensity $\mu_N$, and the recombination probability between position $x$ and the sampled site $0$ is $r_N(x)$. If $N\mu_N \to \mu$ weakly and $(\log 2N)r_N \to r$ uniformly, with $r(0) = 0$ and $r$ monotone on each side of $0$, then the ancestral partition of a sample, with time sped up by $N$, converges in finite-dimensional distributions to the $\Lambda$-coalescent with $\Lambda = \delta_0 + x^2\eta(dx)$, where $\eta([y, 1]) = \int s\,\mathbf 1\{e^{-r(x)/s} \ge y\}\,\mu(dx \times ds)$; convergence in the Skorokhod topology fails because several transitions occur during each short sweep. Sweeps thus add multiple mergers on the same time scale as Kingman's binary mergers, while a rate of sweeps of smaller order makes the multiple mergers disappear in the limit.

## Depends on

- [Pitman's merger rate](../../coalescents/merger-rate.md)

Reduction of the effective size to the mutation-free class in a non-recombining genome under multiplicative mutation–selection balance is a separate statement.

## Expansion

1. Mutation–selection balance at a constrained locus and the fraction of chromosomes free of the deleterious allele.
2. The reduction of neutral diversity for complete linkage, and the separate approximation at recombination fraction $c$, with a common convention for the mutation rate.
3. The Moran model with recurrent beneficial mutations, the scaling of the mutation rate and of the recombination probabilities, and the limiting measure $\Lambda = \delta_0 + x^2\eta(dx)$ (Theorem 2.2).
4. The single-site example with fixed $s$, and the finite-population approximation by a coalescent with simultaneous multiple mergers.
5. Criteria separating a time change of Kingman's coalescent (background selection) from a multiple-merger limit (recurrent sweeps), and the consequences for the site-frequency spectrum.

## Sources

- G. Coop, *Population and Quantitative Genetics*, lecture notes, University of California, Davis, Chapter 13 (The Effects of Linked Selection), section Background selection.
- R. Durrett and J. Schweinsberg, A coalescent model for the effect of advantageous mutations on the genealogy of a population, Stochastic Process. Appl. 115 (2005), 1628–1657, Section 2.3 and Theorem 2.2. <https://arxiv.org/abs/math/0411071>
