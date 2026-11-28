# Optimal projection estimator of individual allele frequencies

**Model.** Let $X \in \{0,1,2\}^{m \times n}$ be the genotype matrix of $m$ SNPs in $n$ individuals and $F = \tfrac12 \mathbb{E}[X] \in [0,1]^{m\times n}$ the matrix of individual-specific allele frequencies. The admixture model assumes that the genotypes are generated independently, $x_{ij} \mid f_{ij} \sim \mathrm{Binomial}(2, f_{ij})$, that $\operatorname{rank} F = d \ll n \ll m$, and that

$$F = PQ,\qquad P \in [0,1]^{m \times d},\qquad Q \in \mathbb{R}_{\ge 0}^{d\times n},\ \ \textstyle\sum_{i} q_{ij} = 1\ \ \forall j,$$

where row $i$ of $P$ holds the frequencies of SNP $i$ in the $d$ ancestral populations and column $j$ of $Q$ the admixture proportions of individual $j$. Write $\langle Q\rangle$ for the row space of $Q$; since $F = PQ$, every row of $F$ lies in $\langle Q\rangle$. For a subspace $\langle S\rangle$ with orthonormal basis $s_1,\dots,s_k$ (row vectors), let $\operatorname{Proj}_{\langle S\rangle}(X) = X\sum_i s_i^{\mathsf T} s_i$.

**Lemma 1 (unbiasedness).** For any random matrix $X$ with $\tfrac12\mathbb{E}[X] = F$ (Lemmas 1 and 2 use only this, not the binomial model), the estimator $\hat F_{\langle S\rangle} = \tfrac12 \operatorname{Proj}_{\langle S\rangle}(X)$ is unbiased for $F$ if and only if $\langle Q\rangle \subseteq \langle S\rangle$.

**Lemma 2 (optimality).** Among all unbiased estimators of this projection form, $\hat F = \tfrac12 \operatorname{Proj}_{\langle Q\rangle}(X)$ minimizes the risk $R(\tilde F, F) = \mathbb{E}\,\|\tilde F - F\|_F^2$.

**Theorem 1 (latent subspace estimation, specialized to the admixture model).** Assume the independent binomial model above, with $n$ and $d$ fixed as $m \to \infty$. Let $\hat\delta_j = \tfrac1m \sum_i (2x_{ij} - x_{ij}^2)$ and $D = \operatorname{diag}(\hat\delta_1,\dots,\hat\delta_n)$. The top $d$ eigenvectors $v_1,\dots,v_d$ of

$$G = \tfrac1m X^{\mathsf T} X - D$$

span $\langle Q\rangle$ asymptotically: with probability 1, $\lim_{m\to\infty} \langle v_1,\dots,v_d\rangle \,\triangle\, \langle Q\rangle = \emptyset$, and the smallest $n - d$ eigenvalues of $G$ converge to $0$.

**Proposition 1 (anchors give identifiability).** Call a factorization $F = PQ$ satisfying the constraints above *anchored* at a set $S$ of $d$ SNPs if, for each $i \in \{1,\dots,d\}$, some row of $P$ in $S$ equals $\delta_i e_i$ with $\delta_i \ne 0$ and $e_i \in \mathbb{R}^d$ the $i$-th unit row vector ("anchor SNPs"). Then any two factorizations of $F$ anchored at the same set $S$ coincide up to a common permutation of the ancestral populations. The same holds for factorizations anchored at a common set of $d$ unadmixed "anchor individuals" (columns of $Q$ with a single nonzero entry, necessarily $1$).

The uniqueness is among anchored factorizations only: an unanchored factorization of the same $F$ can differ. For example, $P = \begin{pmatrix} 0.5 & 0 \\ 0 & 0.5 \\ 0.3 & 0.6 \end{pmatrix}$ and $Q = \begin{pmatrix} 0.4 & 0.6 \\ 0.6 & 0.4 \end{pmatrix}$ give $F = PQ = P'Q'$ with $P' = PM^{-1} = \begin{pmatrix} 0.45 & 0.05 \\ 0.05 & 0.45 \\ 0.33 & 0.57 \end{pmatrix}$ and $Q' = MQ = \begin{pmatrix} 0.375 & 0.625 \\ 0.625 & 0.375 \end{pmatrix}$, where $M^{-1} = \begin{pmatrix} 0.9 & 0.1 \\ 0.1 & 0.9 \end{pmatrix}$; both satisfy the constraints and are not related by a permutation.

## Depends on

- [Parameters of the admixture model](../params.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

Projection onto a subspace missing part of $\langle Q\rangle$ discards signal and is biased; projection onto a larger subspace is unbiased but its extra dimensions fit only noise, which adds variance, so the minimal unbiased choice $\langle Q\rangle$ is risk-optimal. The diagonal correction $D$ uses the binomial model and the independence of the genotypes: it removes the binomial sampling variance from the diagonal of $\tfrac1m X^{\mathsf T}X$, since $\mathbb{E}[x_{ij}^2] = \mathbb{E}[x_{ij}]^2 + \operatorname{Var}(x_{ij})$ and, for $x_{ij} \sim \mathrm{Binomial}(2, f_{ij})$, $\mathbb{E}[2x_{ij} - x_{ij}^2] = 2f_{ij}(1 - f_{ij}) = \operatorname{Var}(x_{ij})$, while independence makes the off-diagonal entries unbiased for those of $\tfrac1m\,\mathbb{E}[X]^{\mathsf T}\mathbb{E}[X]$; what remains is asymptotically a rank-$d$ matrix with row space $\langle Q\rangle$. The resulting $\hat F$ is then factored as $\hat P \hat Q$ under the constraints on $P$ and $Q$ by alternating constrained least squares, whose limit points are stationary by a two-block convergence theorem; every such factorization reproduces the same $\hat F$ and hence the same risk.

## Sources

- I. Cabreros, J. D. Storey, "A likelihood-free estimator of population structure bridging admixture models and principal components analysis", Genetics 212(4) (2019) 1009–1029, Equation (1), Lemmas 1–2, Theorems 1–2 and Appendix A.3 (Proposition 1, whose proof compares two factorizations sharing the anchor rows; the source writes $e_i$ with length $n$, which must be $d$), <https://doi.org/10.1534/genetics.119.302159>, PMCID PMC6707457.
