# Duality of the recombination Moran model and the partitioning process

**Model.** Sequences have linearly ordered sites $S = \{1,\dots,n\}$ with finite allele sets, so types are $x = (x_1,\dots,x_n) \in \mathbb X$. A haploid population of fixed size $N$ is described by the counting measure $Z_t$ on $\mathbb X$. In the **Moran model with single crossovers**, at each event a new individual replaces a uniformly chosen one; with the probability $r_{\mathcal A}$ attached to an ordered two-block partition $\mathcal A = \{\{1,\dots,i\},\{i+1,\dots,n\}\}$ it is assembled from the leading segment of one random parent and the trailing segment of another (crossover between sites $i$ and $i+1$), and otherwise it copies a single parent. In the deterministic limit this drives the normalized type distribution by the *recombinators* $R_{\mathcal A}(\omega) = \|\omega\|^{-2}\,(\pi_{\{1..i\}}.\omega)\otimes(\pi_{\{i+1..n\}}.\omega)$, the normalized product of marginals.

**Sampling functions.** For a partition $\mathcal A = \{A_1,\dots,A_m\}$ of $S$ with $m \le N$, let $H_{\mathcal A}(z)$ be the type distribution obtained from population $z$ by drawing $m$ *distinct* individuals without replacement and taking the sites in $A_i$ from the $i$-th one; it is the normalized version of a counting measure of total mass $N(N-1)\cdots(N-m+1)$.

**Partitioning process.** $(\Sigma_t)$ is a Markov chain on partitions of $S$ describing how the ancestral material of one sampled sequence is spread over ancestors backward in time. A block $A_j$ splits at a crossover into its leading and trailing parts at the rate given by the crossover law restricted to $A_j$; each new part then coalesces with each currently available ancestor block with probability $1/N$, or stays separate. Its generator $\Theta$ has explicit entries.

**Theorem.** The population process $(Z_t)$ and the partitioning process $(\Sigma_t)$ are dual with respect to $H$: for every partition $\mathcal A$ of $S$ and every population state $z$,

$$\mathbb E\big[H_{\mathcal A}(Z_t) \mid Z_0 = z\big] = \mathbb E\big[H_{\Sigma_t}(z) \mid \Sigma_0 = \mathcal A\big].$$

**Limits.** In the deterministic limit $N \to \infty$, the partitioning process converges to a process of *progressive refinements* that only splits blocks, with rate $r_{\mathcal J}$ for splitting $A_j$ into $\mathcal J$; started from an ordered (interval) partition it stays among ordered partitions and recovers the solution of the deterministic recombination equation. In the diffusion limit, with time scaled by $N$, it converges to a process that both splits and merges blocks.

Through the closed linear system it implies, $\frac{d}{dt}\mathbb E\big[H_{\mathcal A}(Z_t)\big] = \sum_{\mathcal B}\Theta_{\mathcal A\mathcal B}\,\mathbb E\big[H_{\mathcal B}(Z_t)\big]$, the duality gives the expected linkage disequilibria in the finite population.

## Expansion

Backward in time, a site set carried by one ancestor is cut by a crossover into the part inherited from the leading parent and the part from the trailing parent; in a finite population the two parents may coincide with ancestors already carrying other blocks, which produces the $1/N$ coalescence of blocks. Sampling without replacement is the right observable because distinct blocks of a partition are carried by distinct individuals. The duality is verified generator by generator: applying the Moran generator to $z \mapsto H_{\mathcal A}(z)$ equals applying $\Theta$ to $\mathcal A \mapsto H_{\mathcal A}(z)$. The generator coincides with one obtained forward in time by a different approach.

## Sources

- Mareike Esser, Sebastian Probst, Ellen Baake, "Partitioning, duality, and linkage disequilibria in the Moran model with recombination", *Journal of Mathematical Biology* 73 (2016), 161–197, <https://doi.org/10.1007/s00285-015-0936-6>; preprint arXiv:1502.05194, <https://doi.org/10.48550/arXiv.1502.05194>. Numbering of the arXiv version: Section 3 (model, recombinators, Definition 1), Section 4 (partitioning process, Propositions 1–2), Section 5 (sampling functions, Proposition 3), Section 6 (duality, Theorem 1), Section 7 (linkage disequilibria).
