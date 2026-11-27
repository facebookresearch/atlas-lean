# Walsh coefficients of a combinatorially complete landscape

Let $n$ biallelic sites define $2^n$ genotypes $g \in \{0,1\}^n$, listed in natural binary order, and let $W = (W_g)$ be the vector of measured phenotypes (fitness, growth rate or drug resistance) of all of them, a combinatorially complete data set. Let $\Psi$ be the $2^n \times 2^n$ Sylvester–Hadamard matrix, $\Psi_{S,g} = (-1)^{|S \cap g|}$ with rows indexed by subsets $S \subseteq \{1, \dots, n\}$ (identified with their indicator vectors) and $|S \cap g| = \sum_{i \in S} g_i$. The **Walsh coefficients** are

$$E = \frac{1}{2^n}\, \Psi W, \qquad E_S = \frac{1}{2^n} \sum_{g} (-1)^{|S \cap g|}\, W_g .$$

$E_\emptyset$ is the mean phenotype, $E_{\{i\}}$ is the main effect of site $i$ and $E_S$ with $|S| = k \ge 2$ is the $k$-th order interaction (epistasis) among the sites in $S$. Since $\Psi \Psi^\top = 2^n I$, the transform is inverted by

$$W_g = \sum_{S} (-1)^{|S \cap g|}\, E_S,$$

and Parseval's identity gives

$$\frac{1}{2^n} \sum_g W_g^2 = \sum_{S} E_S^2, \qquad \frac{1}{2^n} \sum_g (W_g - E_\emptyset)^2 = \sum_{k=1}^{n} \sum_{|S| = k} E_S^2 .$$

Thus the variance of the landscape across genotypes splits exactly into contributions of each epistatic order $k$.

## Depends on

- [Fitness landscapes as mathematical objects](../../../population-genetics/selection-migration-and-transmission/fitness-landscapes/fitness-landscapes-as-explicit-mathematical-obje.md)
- [Fourier coefficient on the subsets of a finite set](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/fourier-coeff.md)

## Proof depends on

- [Fourier inversion on the subsets of a finite set](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/fourier-inversion.md)
- [Plancherel identity on the subsets of a finite set](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/fourier-plancherel.md)

## Expansion

The rows of $\Psi$ are the characters $g \mapsto (-1)^{|S\cap g|}$ of the group $\{0,1\}^n$, which are orthogonal with squared norm $2^n$; this gives the inverse and Parseval's identity, and the variance statement follows by removing the $S = \emptyset$ term. In contrast with background-relative (Möbius) coefficients, which measure each effect relative to the all-zero genotype, Walsh coefficients measure effects relative to the average over all backgrounds, so higher-order terms do not absorb lower-order effects of a particular reference. For $n = 4$ there are $4$ main effects, $6$ pairwise, $4$ three-way and $1$ four-way coefficients. For four resistance mutations in *Plasmodium falciparum* dihydrofolate reductase measured against six antifolates, first- and second-order terms carry most of the sum of squares (for pyrimethamine, fractions $0.653$, $0.317$, $0.029$, $0.001$ for orders $1$ to $4$), while third-order terms still account for about $0.17$–$0.23$ for the triazine antifolates.

## Sources

- E. R. Lozovsky, R. F. Daniels, G. D. Heffernan, D. P. Jacobus and D. L. Hartl, "Relevance of higher-order epistasis in drug resistance", *Molecular Biology and Evolution* (2021), Results section "Main Effects and Their Pairwise and Higher-Order Interactions" and Tables 3–4, <https://doi.org/10.1093/molbev/msaa196> (PMC7782864).
