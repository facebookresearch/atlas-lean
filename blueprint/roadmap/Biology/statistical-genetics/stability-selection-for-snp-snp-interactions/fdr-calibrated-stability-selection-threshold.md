# FDR-calibrated stability selection threshold for interaction screening

**Setting.** Let $\hat S^\lambda(I)=\{k:\hat\theta_k^\lambda(I)\ne0\}$ be the support chosen by a sparse penalized fit (lasso or SCAD) of the SNP-SNP interaction logistic model at penalty $\lambda$ on a random half-sample $I$ of the subjects, with $p=m+m(m-1)/2$ candidate terms. The selection probability of term $k$ is $\hat\Pi_k^\lambda=\mathbb P(k\in\hat S^\lambda(I)\mid X,y)$, estimated from $B$ subsamples. For a region $\Lambda$ of penalties and a cutoff $\pi_{\rm thr}$, the stable set is

$$\hat S^{\rm stable}=\Big\{k:\max_{\lambda\in\Lambda}\hat\Pi_k^\lambda\ge\pi_{\rm thr}\Big\},$$

and $q_\Lambda=\mathbb E\,|\bigcup_{\lambda\in\Lambda}\hat S^\lambda(I)|$ is the expected number of terms selected on a subsample.

**Error bound (Meinshausen-Buhlmann).** If the indicators $\mathbf 1\{k\in\hat S^\lambda\}$ of the noise terms are exchangeable and the base procedure is no worse than random guessing, then for $\pi_{\rm thr}\in(1/2,1]$ the expected number $V$ of falsely selected terms satisfies

$$\mathbb E V\le\frac{1}{2\pi_{\rm thr}-1}\,\frac{q_\Lambda^2}{p}.$$

**Calibration.** Approximating $|\hat S^{\rm stable}|$ by $q_\Lambda$, the false discovery rate obeys

$$\mathrm{FDR}\approx\frac{\mathbb E V}{q_\Lambda}\le\frac{1}{2\pi_{\rm thr}-1}\,\frac{q_\Lambda}{m+m(m-1)/2},$$

so the target $\mathrm{FDR}\le\alpha$ is met by the threshold

$$\pi_{\rm thr}=\frac12\Big(1+\frac{q_\Lambda}{p\,\alpha}\Big),\qquad\text{valid when }q_\Lambda\le p\,\alpha .$$

The source fixes $\Lambda=[\lambda_{\min},\lambda_{\max}]$ from the regularization path ($\lambda_{\max}$ where the first term enters, $\lambda_{\min}$ where $q$ terms have entered, with $q$ about $\sqrt p$ in the discovery stage), estimates $q_\Lambda$ by Monte Carlo, and uses SCAD as the base selector ("stability SCAD").

## Expansion

The bound follows because, under exchangeability, each noise term is selected on a subsample with probability at most $q_\Lambda/p$, and a term is stably selected only if it is selected on both halves of a split often enough; a Markov-type argument on the simultaneous selection frequency gives the factor $1/(2\pi_{\rm thr}-1)$. Dividing by $q_\Lambda$ and solving $q_\Lambda/((2\pi_{\rm thr}-1)p)=\alpha$ for $\pi_{\rm thr}$ gives the calibration, and the condition $q_\Lambda\le p\alpha$ keeps $\pi_{\rm thr}\le1$. Linkage disequilibrium makes exchangeability doubtful for SNP data, so the control is approximate; the source therefore evaluates it by simulation (500 subsamples of 500 cases and 500 controls from 1000-1000 case-control sets) and requires replication across two independent studies.

## Depends on

- [SCAD-penalized logistic model for SNP-SNP interactions](scad-penalized-logistic-model-for-snp-snp-interactions.md)

## Sources

- Gou J, Zhao Y, Wei Y, Wu C, Zhang R, Qiu Y, Zeng P, Tan W, Yu D, Wu T, Hu Z, Lin D, Shen H, Chen F. Stability SCAD: a powerful approach to detect interactions in large-scale genomic study. *BMC Bioinformatics* 15:62 (2014). <https://doi.org/10.1186/1471-2105-15-62> (PMCID: PMC3984751). Theorem 1 (quoted from Meinshausen and Buhlmann), Eqs. (3)-(7).
- Meinshausen N, Buhlmann P. Stability selection. *Journal of the Royal Statistical Society: Series B* 72 (2010) 417-473. <https://doi.org/10.1111/j.1467-9868.2010.00740.x>
