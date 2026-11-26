# Multivariate Bernoulli mixture of gene presence/absence patterns

**Data.** Let $X = (x_{ij})$ be the $F \times N$ binary presence/absence matrix of $F$ gene families in $N$ genomes: $x_{ij} = 1$ iff family $i$ has at least one member in genome $j$. Write $X_i = (x_{ij})_{1 \le j \le N}$.

**Model.** The rows $X_1, \dots, X_F$ are i.i.d. from a $K$-component mixture ($K \ge 3$) of multivariate Bernoulli laws in centroid–dispersion form:

$$P(X_i = x) = \sum_{k=1}^{K} \pi_k \prod_{j=1}^{N} \epsilon_{kj}^{|x_j - \mu_{kj}|}\,(1 - \epsilon_{kj})^{1 - |x_j - \mu_{kj}|},$$

with mixing proportions $\pi_k \in [0,1]$, $\sum_k \pi_k = 1$, binary centroids $\mu_k \in \{0,1\}^N$ (the most probable pattern of partition $k$) and dispersions $\epsilon_{kj} \in [0, \tfrac12]$ (the probability of deviating from the centroid in genome $j$). By default $\epsilon_{kj} = \epsilon_k$ is shared across genomes within a partition. Partition $k$ is persistent if $\mu_k = \mathbf 1$, cloud if $\mu_k = \mathbf 0$, and shell otherwise; $K - 2$ partitions model the shell.

**Estimation.** Parameters are fitted by EM. The triangular initialization $\pi_k = 1/K$, and with $s = 1/\lceil K/2 \rceil$,

$$\mu_{kj} = 1,\ \epsilon_{kj} = s\,k \quad (k \le K/2), \qquad \mu_{kj} = 0,\ \epsilon_{kj} = s\,(K - k + 1) \quad (k > K/2),$$

fixes the labels so that partition $1$ converges to the persistent and partition $K$ to the cloud genome, avoiding label switching. Each family is assigned to its most probable partition if that posterior probability exceeds $\tfrac12$, otherwise to the shell.

**Choosing $K$.** With $\hat\theta$ the (approximate) maximum-likelihood estimate, $\log P_K(X \mid \theta) = \sum_{i} \log \sum_k \pi_k \prod_j \epsilon_{kj}^{|x_{ij} - \mu_{kj}|}(1 - \epsilon_{kj})^{1 - |x_{ij} - \mu_{kj}|}$, and $\dim(K) = K(N + 2)$ when the dispersion is shared within partitions, the integrated completed likelihood is

$$\mathrm{ICL}(K) = \mathrm{BIC}(K) + \sum_{k=1}^{K}\sum_{i=1}^{F} \hat t_{ik} \log \hat t_{ik}, \qquad \mathrm{BIC}(K) = \log P_K(X \mid \hat\theta) - \tfrac12 \dim(K)\log F,$$

where $\hat t_{ik} = p(z_i = k \mid X, \hat\theta)$ are posterior membership probabilities (terms with $\hat t_{ik} = 0$ omitted). The double sum is minus the classification entropy, so ICL is BIC penalized by assignment uncertainty and favours $K$ with high likelihood and confident assignments; $\hat K$ is chosen from the ICL curve over increasing $K$, computed after a few EM steps for each $K$.

## Expansion

With binary centroid $\mu_{kj}$ and dispersion $\epsilon_{kj} \le \tfrac12$, each coordinate is Bernoulli with success probability $1 - \epsilon_{kj}$ if $\mu_{kj} = 1$ and $\epsilon_{kj}$ if $\mu_{kj} = 0$; the parameterization is therefore a reparameterization of the usual Bernoulli mixture that makes the "typical pattern" explicit and identifiable up to the restriction $\epsilon \le \tfrac12$. The E-step computes $\hat t_{ik} \propto \pi_k \prod_j \epsilon_{kj}^{|x_{ij} - \mu_{kj}|}(1 - \epsilon_{kj})^{1 - |x_{ij} - \mu_{kj}|}$; the M-step sets $\pi_k$ to the mean responsibility, $\mu_{kj}$ to the weighted majority value of column $j$, and $\epsilon_{kj}$ to the weighted fraction disagreeing with $\mu_{kj}$. The source describes ICL as BIC penalized by the estimated entropy of the assignments, the criterion of Biernacki, Celeux and Govaert; its printed formula places a minus sign in front of $\sum \hat t \log \hat t$, which would reward uncertainty, so the statement above uses the sign that matches the stated penalty.

## Sources

- G. Gautreau, A. Bazin, M. Gachet, et al., "PPanGGOLiN: depicting microbial diversity via a partitioned pangenome graph", PLoS Computational Biology (2020), Materials and Methods ("Modeling the P/A matrix via a multivariate Bernoulli Mixture Model", "Partitioning of the P/A matrix", "Selection of the optimal number of partitions (K)"), <https://doi.org/10.1371/journal.pcbi.1007732> (PMC7108747).
