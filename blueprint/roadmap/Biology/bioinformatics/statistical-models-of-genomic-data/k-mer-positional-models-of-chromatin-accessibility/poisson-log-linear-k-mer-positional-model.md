# Poisson log-linear $k$-mer positional model of chromatin accessibility

Let $c_i$ be the number of sequencing reads (for instance DNase-seq cuts) assigned to genomic base $i$, $i \in [0,N]$, and let $g^k_i$ denote the $k$-mer starting at base $i$, encoded as an integer index. For each $k \in \{1,\dots,K\}$ let $\theta^k$ be a parameter matrix of size $4^k \times 2M$, whose entry $\theta^k_{(s,\,d)}$ is the additive effect, on the log read rate at offset $d \in [-M, M-1]$, of the $k$-mer $s$ occurring at a given position; let $\theta_0$ be a global offset. The model is log-linear in these positional effects:

$$\lambda_i = \exp\left[ \left( \sum_{k=1}^{K} \sum_{j=-M}^{M-1} \theta^k_{\left(g^k_{i+j},\, -j\right)} \right) - \theta_0 \right],$$

with reads modelled as Poisson with mean $\lambda_i$. Fitting maximizes the $\ell_1$-penalized Poisson log-likelihood

$$\max_{\theta} \;\left( \sum_i c_i \log \lambda_i - \lambda_i \right) - \eta \sum_k \lVert \theta^k \rVert_1 .$$

Because $\log \lambda_i$ is affine in $\theta$, the objective is concave — equivalently its negative is convex — in $\theta$, so the problem has a global optimum that any convergent method attains, independently of the acceleration heuristics used; the gradient with respect to $\theta^k_{(s,j)}$ is the sum of residuals $c_{i+j} - \lambda_{i+j}$ over the positions $i$ at which $k$-mer $s$ occurs, and with respect to $\theta_0$ minus the total residual.

Each $k$-mer thus carries a learned spatial profile of effects on accessibility over a window of $2M$ bases, and effects combine *log-additively*, that is, multiplicatively on the read-rate scale, which is the sense in which sequence features act synergistically rather than additively.

## Remarks

The model treats the whole genome as one continuous regulatory sequence, with no curated set of candidate regions and no discriminative training against a background set, so the parameters are estimated from every base. Log-additivity is the substantive hypothesis, and it is testable: a model in which the same number of parameters combine additively on the read scale, trained identically, predicts held-out chromosomes less well (chromosome-wide Pearson correlation $0.74$) than the log-additive model ($0.82$), which argues that accessibility is governed multiplicatively by cooperating code words. The $\ell_1$ penalty gives sparsity over the $\sum_k 4^k \cdot 2M$ positional effects, and the Poisson link keeps the mean nonnegative and matches the count nature of the data. Evaluation on held-out chromosomes, rather than held-out positions on a trained chromosome, is what makes the fit a genuine prediction, since neighbouring positions share $k$-mers.

## Sources

- T. Hashimoto, R. I. Sherwood, D. D. Kang, et al., "A synergistic DNA logic predicts genome-wide chromatin accessibility", *Genome Research* 26 (2016), 1430–1440, <https://doi.org/10.1101/gr.199778.115> (PMC5052050). Methods, "Model setup" and "Naive inference algorithm"; Results, comparison with the nonsynergistic additive model.
