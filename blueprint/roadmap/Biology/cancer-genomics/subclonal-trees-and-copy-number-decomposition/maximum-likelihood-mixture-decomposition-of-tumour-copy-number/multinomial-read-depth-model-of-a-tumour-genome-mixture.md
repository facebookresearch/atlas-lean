# Multinomial read-depth model of a tumour genome mixture

Partition a reference genome into $m$ non-overlapping intervals $I_1,\dots,I_m$ of equal length. A tumour sample is a mixture of $n$ genomes: a normal genome and $n-1$ cancer genomes. Genome $h$ is described by an interval count vector $c_h \in \mathbb{N}^m$ (the integer number of copies of each interval), with the normal genome fixed at $c_1 = (2,\dots,2)$. Collect these as the interval count matrix $C = [c_{jh}] \in \mathbb{N}^{m\times n}$ and let the genome mixing vector $\mu$ lie in the simplex $\Delta_{n-1} = \{\mu \in \mathbb{R}^n_{\ge 0} : \sum_h \mu_h = 1\}$.

**Model.** Assume read start positions are uniform over the DNA in the sample (Lander–Waterman assumptions) and reads align uniquely. Then a read aligns to $I_j$ with probability equal to the fraction of sample DNA coming from $I_j$:

$$p_j = \frac{(C\mu)_j}{\lVert C\mu \rVert_1}, \qquad p = \widehat{C\mu} := \frac{C\mu}{\lVert C\mu\rVert_1},$$

and the observed read depth vector $r = (r_1,\dots,r_m) \in \mathbb{N}^m$ with $N = \sum_j r_j$ is a draw from $\mathrm{Mult}(N; \widehat{C\mu})$. The counts are dependent: a large deletion changes the expected count in every other interval.

**Negative log-likelihood.** Up to an additive constant depending only on $r$,

$$\mathcal{L}_r(C,\mu) = -\sum_{i=1}^m r_i \log\big(\widehat{C\mu}\big)_i .$$

For $N \ge 1$ (with $0 \log 0 = 0$), the unique minimiser over the whole simplex $p \in \Delta_{m-1}$ is $p^*_i = r_i/N$.

**Identifiability and reduction to convex problems.** Only $p = \widehat{C\mu}$ is identifiable from $r$: pairs $(C,\mu) \neq (C',\mu')$ with $\widehat{C\mu} = \widehat{C'\mu'}$ have identical likelihood for every $r$. Moreover, if $p = \widehat{C\mu}$ then there is $\mu' \in \Delta_{n-1}$ with

$$p = \hat C \mu', \qquad \hat C = (\hat c_1,\dots,\hat c_n),$$

so for fixed $C$ the feasible set is the convex hull $H(C) = \{\hat C\mu : \mu \in \Delta_{n-1}\}$ of the normalised columns. Since $\mathcal{L}_r(p)$ is separable convex, the maximum likelihood mixture decomposition problem

$$\min \mathcal{L}_r(p) \quad \text{subject to} \quad p \in \bigcup_{C} H(C)$$

is a disjunction of convex programmes, one per admissible count matrix (for example all $C$ with entries in $\{0,\dots,k\}$). The union is not convex, and the number of candidate matrices is exponential in $m$ and $n$ in general.

**Unequal interval lengths.** With interval weights $w_j > 0$ (length or mappability) and $W = \mathrm{diag}(w)$, the read distribution becomes $\mathrm{Mult}(N; \Phi(C\mu))$ with $\Phi(v) = \widehat{Wv}$.

## Expansion

The multinomial (rather than independent-Poisson) form comes from conditioning on the total read count $N$: each read independently lands in interval $j$ with probability proportional to the amount of DNA there. The reparametrisation $\widehat{C\mu} = \hat C\mu'$ follows by writing $C\mu = \sum_h \mu_h \lVert c_h\rVert_1 \hat c_h$ and renormalising the weights $\mu_h\lVert c_h\rVert_1$ to sum to one. Fixing $C$ then leaves a log-concave likelihood over a polytope. The non-identifiability of $(C,\mu)$ is why tumour purity and ploidy cannot be resolved from depth alone without extra constraints such as a copy-number cap or an expected ploidy.

## Sources

- L. Oesper, A. Mahmoody, B. J. Raphael, *THetA: inferring intra-tumor heterogeneity from high-throughput DNA sequencing data*, Genome Biology 14 (2013), R80, Materials and methods (Eqs. 1–6, Theorem 1). <https://doi.org/10.1186/gb-2013-14-7-r80> (PMCID: PMC4054893)
