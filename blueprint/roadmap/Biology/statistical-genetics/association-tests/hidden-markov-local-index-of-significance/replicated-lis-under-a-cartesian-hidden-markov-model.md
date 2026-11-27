# Replicated LIS under a Cartesian hidden Markov model

**Replicability null.** Two association studies test the same $m$ SNPs. Let $H_{i,j}\in\{0,1\}$ indicate that SNP $j$ is associated in study $i=1,2$. The no-replicability null for SNP $j$ is

$$\mathcal H^{NR}_{0j}:\ (H_{1,j},H_{2,j})\in\{(0,0),(1,0),(0,1)\},$$

i.e. association in at most one study, and a discovery ($\delta_j=1$) claims association in both.

**Cartesian hidden Markov model.** The pairs $(H_{1,j},H_{2,j})_{j=1}^m$ form a stationary, irreducible, aperiodic four-state Markov chain with transitions $A_{uv}=P\bigl((H_{1,j+1},H_{2,j+1})=v\mid(H_{1,j},H_{2,j})=u\bigr)$ and initial law $\pi=(\pi_{00},\pi_{10},\pi_{01},\pi_{11})$. Given the states, the z-values $z_{i,j}=\Phi^{-1}(1-p_{i,j})$ are independent with

$$Z_{i,j}\mid H_{i,j}\sim(1-H_{i,j})f_{i0}+H_{i,j}f_{i1},$$

typically $f_{i0}=N(0,1)$ and $f_{i1}=N(\mu_i,\sigma_i^2)$.

**repLIS statistic and procedure.**

$$\mathrm{repLIS}_j=P\bigl(\mathcal H^{NR}_{0j}\text{ true}\mid\{z_{1,i}\}_{i=1}^m,\{z_{2,i}\}_{i=1}^m\bigr).$$

Order $\mathrm{repLIS}_{(1)}\le\dots\le\mathrm{repLIS}_{(m)}$ and reject $\mathcal H^{NR}_{0(1)},\dots,\mathcal H^{NR}_{0(l)}$ with $l=\max\{t:\ \tfrac1t\sum_{j=1}^t\mathrm{repLIS}_{(j)}\le\alpha\}$.

**Theorem.** Under the Cartesian HMM with known parameters, the repLIS procedure controls the FDR at level $\alpha$, and its FNR is $\beta^*+o(1)$, where $\beta^*$ is the smallest FNR among all $\alpha$-level FDR procedures.

**Computation.** With forward variables $\alpha_j(p,q)=P\bigl((H_{1,j},H_{2,j})=(p,q),\{z_{1,i}\}_{i\le j},\{z_{2,i}\}_{i\le j}\bigr)$ and backward variables $\beta_j(p,q)=P\bigl(\{z_{1,i}\}_{i>j},\{z_{2,i}\}_{i>j}\mid(H_{1,j},H_{2,j})=(p,q)\bigr)$,

$$\mathrm{repLIS}_j=1-\frac{\alpha_j(1,1)\beta_j(1,1)}{\sum_{p,q\in\{0,1\}}\alpha_j(p,q)\beta_j(p,q)},$$

$$\alpha_{j+1}(p,q)=\sum_{s,t}\alpha_j(s,t)\,A_{(s,t)(p,q)}\,f_{1p}(z_{1,j+1})f_{2q}(z_{2,j+1}),\quad \beta_j(p,q)=\sum_{s,t}A_{(p,q)(s,t)}\,f_{1s}(z_{1,j+1})f_{2t}(z_{2,j+1})\,\beta_{j+1}(s,t).$$

In practice the parameters are replaced by EM estimates (plug-in repLIS).

## Expansion

Under the weighted classification loss $\frac1m\sum_j\bigl[\lambda\,\mathbf 1\{\text{null}\}\delta_j+H_{1,j}H_{2,j}(1-\delta_j)\bigr]$ the Bayes rule thresholds $\Lambda_j=\mathrm{repLIS}_j/(1-\mathrm{repLIS}_j)$, which is monotone in $\mathrm{repLIS}_j$. Thresholding the running mean of ordered posterior null probabilities then gives marginal FDR control at the largest rejection set, and mFDR and FDR agree up to $O(1/\sqrt m)$. The Markov chain on the product state space lets a strong signal in one study and moderate evidence at neighbouring SNPs in the other combine, so whole clusters of replicated SNPs are detected rather than only the SNPs with the smallest p-values.

## Depends on

- [Region-specific pooled LIS procedure](region-specific-pooled-lis-procedure.md)
- [Hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/hmm.md)

## Proof depends on

- [Forward variables of a hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/forward.md)

## Sources

- P. Wang, W. Zhu, "Replicability analysis in genome-wide association studies via Cartesian hidden Markov models", *BMC Bioinformatics* 20 (2019), Equations (1)–(6), Theorem 1, and the forward–backward and EM sections of Methods, <https://doi.org/10.1186/s12859-019-2707-7>, PMCID PMC6423849.
