# Composite likelihoods for genetic data and their uncertainty

A composite likelihood multiplies component likelihoods, such as those of single sites or pairs of sites; it is a genuine likelihood only when the components are independent. The frequency spectrum of unlinked SNPs gives such an independent-site likelihood (Adams and Hudson 2004, abstract and Introduction), while linkage makes sites dependent, so the corresponding product over linked sites is a composite likelihood, as in the composite-likelihood estimator of the recombination parameter from more than two linked sites built from two-locus sampling probabilities (Hudson 2001, abstract). For a composite score $u(\theta; y)$, Varin, Reid and Firth (2011, Section 2) distinguish the sensitivity matrix $H(\theta) = E_\theta\{-\nabla_\theta u(\theta; Y)\}$ from the variability matrix $J(\theta) = \mathrm{var}_\theta\{u(\theta; Y)\}$, since the second Bartlett identity fails, and replace the Fisher information by the Godambe information

$$G(\theta) = H(\theta)J(\theta)^{-1}H(\theta)$$

(equation (2.4)). For $n$ independent replicates, $\sqrt n(\hat\theta_{CL} - \theta) \to N_p(0, G(\theta)^{-1})$; Wald and score statistics built with $G$ have the usual $\chi^2_q$ limits; and the composite likelihood ratio statistic for a $q$-dimensional parameter of interest converges to $\sum_{j=1}^q \lambda_j Z_j^2$, with $\lambda_j$ the eigenvalues of $(H^{\psi\psi})^{-1}G_{\psi\psi}$ and $Z_j$ independent standard normals (equation (2.5)), not to $\chi^2_q$. The same authors note that for increasing dimension with fixed sample size, the case relevant to genetics, there is no rigorous proof that the composite maximum likelihood estimator is or is not consistent (Section 6.2).

## Expansion

1. Independent-site likelihoods for unlinked data, and composite likelihoods for linked sites.
2. Sensitivity and variability matrices, and the Godambe information (2.4).
3. Asymptotic normality of the composite maximum likelihood estimator with variance $G^{-1}$, under replication or a central limit theorem for the score of dependent sites along the genome.
4. Wald and score statistics, the weighted chi-square limit of the composite likelihood ratio, and its Satterthwaite-type adjustments.
5. The open consistency question for long genomes with a fixed number of samples.

## Sources

- C. Varin, N. Reid and D. Firth, An overview of composite likelihood methods, Statist. Sinica 21 (2011), 5–42, Sections 2.2–2.3 (equations (2.4), (2.5)) and Section 6.2.
- A. M. Adams and R. R. Hudson, Maximum-likelihood estimation of demographic parameters using the frequency spectrum of unlinked single-nucleotide polymorphisms, Genetics 168 (2004), 1699–1712, abstract and Introduction. <https://doi.org/10.1534/genetics.104.030171>
- R. R. Hudson, Two-locus sampling distributions and their application, Genetics 159 (2001), 1805–1817, abstract. <https://doi.org/10.1093/genetics/159.4.1805>
