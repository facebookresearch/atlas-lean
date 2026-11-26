# Expected IBD sharing from coalescence times and Erlang segment lengths

Fix a genomic site and a pair of haploid genomes whose most recent common ancestor at that site lived $t$ generations ago, with $t$ measured continuously. Let $\pi_{\boldsymbol\theta}(t)$ be the density of this coalescence time under a demographic model $\boldsymbol\theta$, and let $f(\ell \mid t)$ be the density of the genetic length $\ell$ (in Morgans) of the maximal shared haplotype spanning the site. Recombination occurs on either side of the site along the $2t$ meioses separating the two genomes, so the distance to the first breakpoint on each side is exponential with rate $2t$ and the total length is the sum of two such distances: $\ell \mid t \sim \mathrm{Erlang}(2, 2t)$. The probability that the site lies inside a shared segment whose length falls in a range $R = [u, v]$ is

$$\Pr[\ell \in R \mid \boldsymbol\theta] \;=\; \int_0^\infty \pi_{\boldsymbol\theta}(t) \int_u^v f(\ell \mid t)\, d\ell\, dt ,$$

and by linearity of expectation this quantity equals the **expected fraction of the genome** shared by the pair through segments with length in $R$. In a Wright–Fisher population of constant size $N_e$ one has $\pi(t) = e^{-t/N_e}/N_e$ and the double integral has a closed form.

Three consequences follow from the same quantity: over a region of genetic length $\gamma$ the number of shared segments with length in $R$ is Poisson with mean $\gamma$ times the per-site probability divided by the mean segment length in $R$; the length of a randomly sampled shared segment has density proportional to $\int_0^\infty \pi(t) f(\ell\mid t)\,dt$ restricted to $R$; and the whole distribution of the shared genome fraction, not only its mean, is determined by $\pi_{\boldsymbol\theta}$.

## Expansion

The key structural point is that the demographic model enters only through the coalescence-time density $\pi_{\boldsymbol\theta}(t)$: segment lengths are conditionally independent of demography given $t$. Any model — constant size, piecewise changes, splits, migration between subpopulations — can therefore be fitted by substituting its own $\pi_{\boldsymbol\theta}$. Taking the limit of the resulting estimator as $v \to \infty$ gives the closed-form estimator of recent effective size from the average genome fraction shared through segments longer than a threshold $u$; that estimator is biased upward when migration is present and ignored, approaching the summed size of the exchanging populations as the migration rate grows. Extremely ancient demographic events contribute negligibly, because they produce segments far shorter than the detection threshold, so it is safe to assume a constant ancestral size beyond some generation, which also makes the integral tractable.

## Sources

- P. F. Palamara, I. Pe'er, "Inference of historical migration rates via haplotype sharing", *Bioinformatics* 29 (2013), i180–i188, <https://doi.org/10.1093/bioinformatics/btt239> (PMC3694674). Methods, "Haplotype sharing and demographic history", Equations (1)–(3).
