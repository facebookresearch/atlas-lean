# iCluster joint latent-variable model

Let $n$ tumours be profiled on $T$ molecular platforms, with centred data matrices $X_t \in \mathbb R^{p_t \times n}$, $t = 1, \dots, T$ (rows are features, columns are tumours). To find $K$ subtypes, iCluster posits a common latent matrix $Z \in \mathbb R^{(K-1) \times n}$ and platform-specific loading matrices $W_t \in \mathbb R^{p_t \times (K-1)}$ with

$$X_t = W_t Z + E_t, \qquad t = 1, \dots, T,$$

where the columns of $Z$ are independent $\mathcal N(0, I_{K-1})$ and the columns of $E_t$ are independent $\mathcal N(0, \Psi_t)$ with $\Psi_t$ diagonal, independent of $Z$ and across platforms. Stacking $X = (X_1; \dots; X_T)$, $W = (W_1; \dots; W_T)$ and $\Psi = \operatorname{diag}(\Psi_1, \dots, \Psi_T)$ gives a Gaussian factor model whose columns satisfy $x \sim \mathcal N(0, WW^\top + \Psi)$. The parameters are estimated by an EM algorithm (with a lasso penalty on $W$ for sparse feature selection), and the posterior mean of the latent variables,

$$\mathbb E[Z \mid X] = W^\top (WW^\top + \Psi)^{-1} X,$$

is clustered into $K$ groups by $k$-means.

## Expansion

The latent dimension $K - 1$ mirrors the fact that $K$ well-separated cluster centroids span a $(K-1)$-dimensional affine subspace; the Gaussian factor model then plays the role of a probabilistic relaxation of $k$-means in which cluster membership is encoded by the latent coordinates. Because one $Z$ drives every platform, the posterior mean pools evidence across data types, with each platform weighted through its loadings and noise variances; the penalty on $W_t$ selects informative features per platform. The EM updates are those of factor analysis: the E-step computes $\mathbb E[Z \mid X]$ and $\mathbb E[ZZ^\top \mid X]$, and the M-step updates $W$ and $\Psi$ by (penalized) regression of $X$ on the expected latent variables. Hoadley et al. applied iCluster to copy number, DNA methylation, mRNA and miRNA data from about 10,000 tumours of 33 cancer types and obtained 28 integrated subtypes dominated by cell-of-origin patterns.

## Sources

- R. Shen, A. B. Olshen, M. Ladanyi, "Integrative clustering of multiple genomic data types using a joint latent variable model with application to breast and lung cancer subtype analysis", Bioinformatics 25 (2009), 2906–2912, <https://doi.org/10.1093/bioinformatics/btp543>.
- K. A. Hoadley, C. Yau, T. Hinoue, et al., "Cell-of-origin patterns dominate the molecular classification of 10,000 tumors from 33 types of cancer", Cell 173 (2018), 291–304, <https://doi.org/10.1016/j.cell.2018.03.022> (PMC5957518), STAR Methods "Integrative clustering with iCluster".
