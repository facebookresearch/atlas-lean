# Lognormal–negative binomial null for Tn-Seq read counts (FiTnEss)

In a transposon insertion sequencing experiment with a mariner-type transposon, let gene $g$ contain $N_g$ usable TA insertion sites and let $n_g$ be the total number of reads mapped to those sites. The FiTnEss null model for **nonessential** genes is hierarchical: the gene has a fitness parameter $p_g \in (0,1)$ with

$$\frac{1}{p_g} \sim \mathrm{LogNormal}(\mu, \sigma^2),$$

and, given $p_g$, the read counts at its TA sites are independent geometric variables on $\{0, 1, 2, \dots\}$ with success probability $p_g$, independent of $N_g$. Hence, given $p_g$, the gene total is negative binomial,

$$n_g \mid p_g \sim \mathrm{NegBin}(N_g, p_g), \qquad \mathbb P(n_g = n \mid p_g) = \binom{n + N_g - 1}{n} p_g^{N_g}(1-p_g)^n,$$

and marginally $n_g$ follows a lognormal mixture of negative binomials. The two parameters $(\mu, \sigma)$ are fitted per dataset on genes confidently nonessential (the upper part of the reads-per-gene distribution). A gene is tested by the lower-tail p-value

$$\pi_g = \mathbb P\big(n^*_{N_g} \le n_g\big),$$

where $n^*_{N_g}$ has the null distribution for genes with $N_g$ sites; p-values are adjusted across genes by the Holm–Bonferroni (family-wise error) or Benjamini–Hochberg (false discovery rate) procedure, and a gene is called essential when its adjusted p-value is below $0.05$ in both replicates.

## Expansion

A sum of $N$ independent geometric variables with common success probability $p$ is negative binomial with size $N$, so the only gene-specific input besides the counts is the number of insertion sites, which governs detection power: genes with few TA sites cannot be called essential with confidence however few reads they have. Random effects on $1/p_g$ capture gene-to-gene fitness variation among nonessential genes; the lognormal shape reproduces the bimodal reads-per-gene distribution, with essential genes forming the low mode. Poulsen et al. verified the assumption that per-site read counts do not depend on gene length by comparing randomly sampled TA sites across genes of different sizes, computed the null distribution for each $N_g$ category by numerical sampling, and validated calls against clean gene deletions. Applied to nine *Pseudomonas aeruginosa* strains on five media, the model defined 321 core essential genes.

## Sources

- B. E. Poulsen, R. Yang, A. E. Clatworthy, et al., "Defining the core essential genome of *Pseudomonas aeruginosa*", Proceedings of the National Academy of Sciences USA 116 (2019), <https://doi.org/10.1073/pnas.1900570116> (PMC6525520), Results "FiTnEss: A Statistical Model to Identify Essential Genes" and Materials and Methods.
