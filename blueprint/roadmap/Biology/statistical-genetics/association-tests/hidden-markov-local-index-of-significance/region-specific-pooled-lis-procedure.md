# Region-specific pooled LIS procedure

**Model.** Chromosome $c=1,\dots,C$ is split by change points $w_c$ into regions $r=1,\dots,R_c$ with $L_{cr}$ SNPs. Let $\theta^{(c)}_{rl}\in\{0,1\}$ indicate that SNP $l$ of region $r$ is disease-associated and $Z^{(c)}_{rl}$ its z-value (from a case–control $\chi^2$ p-value). Assume that, given the hidden states, the z-values are independent, with

$$Z^{(c)}_{rl}\mid\theta^{(c)}_{rl}\sim(1-\theta^{(c)}_{rl})\,N(0,1)+\theta^{(c)}_{rl}\sum_{i=1}^{m_c}\xi_i\,N\bigl(\mu^{(c)}_{ri},\sigma^{(c)2}_{ri}\bigr),$$

the number of mixture components $m_c$ being common to the regions of a chromosome. Assume also that the hidden states of different regions are independent, and that within region $r$ they form a stationary two-state Markov chain with transition matrix $\Lambda_{cr}=(a^{(c)}_{rij})$ and stationary law $\pi^{(c)}_{r0}=a^{(c)}_{r10}/(a^{(c)}_{r10}+a^{(c)}_{r01})$. Write $\Psi_{cr}$ for the parameters of region $r$; in practice they are fitted by EM.

**Model selection.** Change points and $m_c$ are chosen by minimizing the penalized criterion

$$\mathrm{crit}_{\lambda_c}(m_c,w_c)=-\ln P\bigl(Z^{(c)}\mid\hat\Psi_c,m_c,w_c\bigr)+\lambda_c\,D(m_c,w_c),\qquad D(m_c,w_c)=(|w_c|+1)D_{m_c},$$

over subsets of candidate haplotype-block boundaries, by dynamic programming. The choice $\lambda_c=\tfrac12\ln L_c$ ($L_c=\sum_rL_{cr}$) is BIC for the HMM; instead $\lambda_c$ is calibrated from the data by a sliding-window dimension-jump (slope-heuristic) method.

**Procedure (RSPLIS).**

1. For every SNP compute the plug-in local index of significance $\mathrm{LIS}^{(c)}_{rl}=P_{\hat\Psi_{cr}}\bigl(\theta^{(c)}_{rl}=0\mid Z^{(c)}_r\bigr)$ by the forward–backward algorithm.
2. Pool the $L=\sum_c\sum_rL_{cr}$ values across all regions and chromosomes and order them, $\mathrm{LIS}_{(1)}\le\dots\le\mathrm{LIS}_{(L)}$, with hypotheses $H_{(1)},\dots,H_{(L)}$.
3. Reject $H_{(1)},\dots,H_{(l)}$ with $l=\max\{i:\ \tfrac1i\sum_{j=1}^i\mathrm{LIS}_{(j)}\le\alpha\}$.

**Theorem.** Consider the multi-region HMM above with known change points $w_c$ and known numbers of components $m_c$, and let the procedure use the LIS values $P_{\Psi_{cr}}\bigl(\theta^{(c)}_{rl}=0\mid Z^{(c)}_r\bigr)$ computed from the model's parameters. Then RSPLIS controls the global FDR at level $\alpha$, and its global false non-discovery rate is $\beta^*+o(1)$, where $\beta^*$ is the smallest FNR among all valid FDR procedures at level $\alpha$.

## Depends on

- [Hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/hmm.md)

## Proof depends on

- [Forward variables of a hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/forward.md)

## Expansion

The running mean $\tfrac1i\sum_{j\le i}\mathrm{LIS}_{(j)}$ estimates the false discovery proportion of the top $i$ hypotheses, because each LIS is the posterior probability that its hypothesis is null; pooling all regions before thresholding spends the error budget where signals are, instead of fixing a level per region. The compound decision-theoretic optimality of LIS ranking under HMM dependence carries over because regions are independent and each has its own correctly specified HMM. Allowing region-specific parameters accommodates the different LD and signal patterns along a chromosome, which a single chromosome-wide HMM averages out. The theorem does not cover the data-driven change points, the selected $m_c$ or the EM plug-in estimates that the procedure uses in practice.

## Sources

- J. Xiao, W. Zhu, J. Guo, "Large-scale multiple testing in genome-wide association studies via region-specific hidden Markov models", *BMC Bioinformatics* 14 (2013), Methods: region-specific multi-HMM, Equation (1) and Algorithms 1–2 (adaptive criterion-based partitioning), pooled FDR control procedure (Steps 1–3) and Theorem 1, <https://doi.org/10.1186/1471-2105-14-282>, PMCID PMC3850654.
