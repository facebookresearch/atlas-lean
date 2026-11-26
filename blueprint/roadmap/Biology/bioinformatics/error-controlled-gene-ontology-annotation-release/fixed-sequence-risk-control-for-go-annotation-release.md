# Fixed-sequence risk control for hierarchy-aware GO annotation release

**Release problem.** A predictor gives a score $s_{ig}$ for each gene $i$ and Gene Ontology (GO) term $g$. A release policy $\pi$ gives each gene a released set $S_i(\pi)$; a global threshold uses $S_i(\lambda)=\{g:s_{ig}\ge\lambda\}$. Let $A_i^{\mathrm{TP}}$ be the reference annotations of gene $i$ closed upward under the GO hierarchy (true-path closure; scores are not propagated). The **gene-level false discovery proportion** is
$$L_i(S_i)=1-\frac{|S_i\cap A_i^{\mathrm{TP}}|}{|S_i|}\quad(|S_i|>0),\qquad L_i(\emptyset)=0,$$
so every gene has equal weight and abstention costs nothing. For a fixed panel split into ranking, certification and evaluation folds, the risk of a policy is the mean FDP over the non-ranking pool $\mathcal P$ of size $N$, $R(\pi)=\frac1N\sum_{i\in\mathcal P}L_i(\pi)$, with target $\alpha$.

**Nested candidate paths.** Using only ranking-fold labels and frozen inputs, build a sequence of policies whose released sets only grow. GoCo-M inserts partial admissions within tied-score blocks: genes sharing module evidence get identical scores, and genes are admitted in an order learned from source reliability. GoCo-N orders individual calls by their predicted probability of being unsupported. Certification computes each candidate's mean FDP $\hat R_k$ and standard deviation $\hat s_k$ on the $m$ certification genes, sets $p_k=\Phi\big((\hat R_k-\alpha)/(\max(\hat s_k,10^{-6})/\sqrt m)\big)$, tests candidates in their fixed order, stops at the first $p_k>\delta$, and releases the preceding policy $\hat\pi$ (abstaining if the first fails).

**Proposition (conditional fixed-sequence risk control).** Let $k^*$ be the first candidate on the path with $R(\pi_{k^*})>\alpha$. Suppose $m\to\infty$, $N-m\to\infty$, $m/N\to f\in[0,1)$, and the pool variance of the losses of $\pi_{k^*}$ stays bounded away from zero. Then, conditional on the ranking fold,
$$\limsup\ \Pr\{R(\hat\pi)>\alpha\mid\mathcal T\}\le\Phi\big(z_\delta/\sqrt{1-f}\big)\le\delta,\qquad z_\delta=\Phi^{-1}(\delta),\ \delta\in(0,\tfrac12],$$
with equality in the second inequality only when $\delta=\frac12$ or $f=0$. The bound holds for any ranking-fold-measurable ordering within blocks. Replacing the normal test by Hoeffding's bound gives finite-sample control on the same path.

## Expansion

If the released policy has risk above $\alpha$, the first invalid candidate on the prespecified path must have passed its test, so the error probability is at most the probability that a single fixed invalid policy passes. Its pool losses are constants once the path is fixed, and certification genes are a simple random sample without replacement from the pool, so a finite-population central limit theorem (Hájek, Erdős-Rényi) applies without assuming independent gene losses, which matters because genes in shared modules have strongly dependent errors. The finite-population correction $\sqrt{1-f}$ makes the normal test conservative. On co-essentiality-module and network-neighbourhood predictors validated on independent studies, the structure-guided paths kept held-out gene-level FDP at or below target while releasing about 6 to 36% more reference-supported GO terms than global multilabel calibration.

## Sources

- C. Wang, Y. Shao, P. Liu, "GoCo: structure-guided conformal calibration for error-controlled Gene Ontology annotation release", arXiv:2610.32990 (2026), Section 2.1 (gene-level FDP with true-path closure), Section 2.2 (risk and splits), Section 2.3 (GoCo-M and GoCo-N paths), Section 2.4 (Proposition 1) and Section 3 (results), <https://doi.org/10.48550/arXiv.2610.32990>.
