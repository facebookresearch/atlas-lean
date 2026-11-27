# Minimum error correction as structured low-rank factorization

Consider $m$ variant sites, $k$ haplotypes and $n$ reads. Encode each allele as a standard basis vector in $\{0,1\}^4$ (so biallelic and polyallelic sites are handled uniformly). The reads form a binary tensor $\mathcal R \in \{0,1\}^{n \times m \times 4}$, whose fibre $\mathcal R_{ij:}$ is the allele of read $i$ at site $j$ (zero if uncovered), and the haplotypes a tensor $\mathcal V \in \{0,1\}^{m \times k \times 4}$. Let $\Omega_i$ be the sites covered by read $i$, $\Omega = \bigcup_i \Omega_i$, $P_\Omega$ the projection keeping entries in $\Omega$, $d(\cdot,\cdot) \in \{0,1\}$ the mismatch indicator on covered fibres, and $\bar R \in \{0,1\}^{n \times 4m}$, $\bar V \in \{0,1\}^{4m \times k}$ the mode-1 unfoldings.

**MEC and CPR.** The minimum error correction score and correct phasing rate are

$$\mathrm{MEC} = \sum_{i=1}^n \min_{p \in [k]} \sum_{j=1}^m d(\mathcal R_{ij:}, \mathcal V_{jp:}), \qquad \mathrm{CPR} = 1 - \frac{1}{mk}\min_{\mathcal M}\sum_{i,j} d\big(\mathcal M(\mathcal V)_{ij:}, \mathcal V^{t}_{ij:}\big),$$

with $\mathcal M$ ranging over matchings of reconstructed to true haplotypes.

**Factorization identity.** Since a mismatching one-hot pair has squared distance $2$,

$$\mathrm{MEC} = \min_{U, \bar V}\ \tfrac12 \big\|P_\Omega\big(\bar R - U\bar V^{\top}\big)\big\|_F^2,$$

where each row of $U \in \{0,1\}^{n \times k}$ is a standard basis vector assigning the read to one haplotype. Relaxing $\bar V_{ij} \in \{0,1\}$ to $[0,1]$ gives a problem convex in each factor separately, solved by alternating an exhaustive row-wise update of $U$ with projected gradient steps $\bar V \leftarrow \Pi_{[0,1]}(\bar V - \alpha\nabla f(\bar V))$; the step $\alpha = C\|\nabla f\|_F^2 / \|P_\Omega(U\nabla f^\top)\|_F^2$ with $C \in (0, 2)$ makes the objective nonincreasing.

**Recovery guarantee.** Let $\bar M = U\bar V^\top$ be $\mu$-incoherent with condition number $\kappa$, fibres observed independently with probability $p$, $C_{\mathrm{snp}} = mp$, $C_{\mathrm{seq}} = np$ and read error rate $p_e$. There are constants $C_0, C_1$ such that if

$$C_{\mathrm{snp}} > \max\Big\{C_0\,\big(\mu^4 k^{14}\kappa^{12} C_{\mathrm{seq}}\big)^{1/3},\ \frac{p_e k^2 \kappa^6}{2C_1}\Big\},$$

then with probability at least $1 - m^{-3}$ the alternating solution satisfies $\|\bar M - U^*\bar V^{*\top}\|_F^2 \le C_1\kappa^4 p_e k m / (2C_{\mathrm{snp}})$, and $\mathbb E\{\mathrm{MEC}\} \le 2p_e\big(C_{\mathrm{seq}} m + \kappa^4 C_1 k\big)$.

## Expansion

Writing each read's best haplotype as the argmin of a squared Frobenius distance and stacking the indicator rows into $U$ converts the minimum over assignments into a minimum over a binary factor, so MEC is exactly a masked rank-$k$ factorization with combinatorial constraints. The alternating scheme decreases $f$ because each subproblem is convex and the box $[0,1]$ is convex. The guarantee follows from matrix-completion perturbation analysis showing local convexity around the global optimum, combined with a spectral initialization; the error term grows with the sequencing error rate and the number of haplotypes, so polyploid assembly is harder than diploid at equal coverage.

## Sources

- A. Hashemi, B. Zhu, H. Vikalo, "Sparse tensor decomposition for haplotype assembly of diploids and polyploids", BMC Genomics 19 (Suppl 4) (2018) 191, Methods, Eqs. 4–16, Definition 1 and Theorems 1–2, <https://doi.org/10.1186/s12864-018-4551-y>, PMCID PMC5872563.
