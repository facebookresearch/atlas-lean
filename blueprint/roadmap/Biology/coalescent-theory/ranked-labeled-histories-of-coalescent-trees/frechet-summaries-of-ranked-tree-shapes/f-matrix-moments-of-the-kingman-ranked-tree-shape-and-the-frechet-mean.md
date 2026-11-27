# $\mathbf F$-matrix moments of the Kingman ranked tree shape and the Fréchet mean tree

**Setting.** A *ranked tree shape* with $n$ leaves is a rooted binary tree with unlabelled leaves whose $n-1$ internal nodes are totally ordered in time. The internal nodes get ranks $2,\dots,n$ from the root (rank $2$) towards the leaves, and the leaves are treated as rank $n+1$. The time interval $I_j$, $1\le j\le n-1$, lies between the nodes of ranks $j+1$ and $j+2$, so $I_1$ is the interval just below the root, where two lineages are extant. (The source writes "between ranks $j$ and $j+1$", which would put $I_1$ above the root and contradict $F_{1,1}=2$.) It is encoded bijectively by an $(n-1)\times(n-1)$ lower-triangular integer **$\mathbf F$-matrix**. The diagonal entry $F_{i,i}=i+1$ counts the lineages in interval $I_i$, the subdiagonal is $F_{i+1,i}=i$, and the off-diagonal entry $F_{i,j}$ ($j<i$) counts the branches extant in $I_j$ that do not bifurcate before $I_i$. The $\mathbf F$-matrices form a set $\mathcal F_n$ cut out by explicit linear inequalities. Two metrics on ranked tree shapes are the entrywise distances $d_1(F_1,F_2)=\sum_{i,j}|(F_1)_{ij}-(F_2)_{ij}|$ and $d_2(F_1,F_2)=\big(\sum_{i,j}((F_1)_{ij}-(F_2)_{ij})^2\big)^{1/2}$.

For a probability mass function $\mu$ on $\mathcal F_n$, a **Fréchet mean tree** is any

$$\bar T\in\arg\min_{x\in\mathcal F_n}\ \sum_{y\in\mathcal F_n} d(x,y)^2\,\mu(y).$$

It exists because $\mathcal F_n$ is finite, though it need not be unique. For $d=d_2$, write $M=\mathbb E_\mu[F]$ for the entrywise mean matrix. Then $\sum_y d_2(x,y)^2\mu(y)=\|x-M\|_2^2+\mathbb E_\mu\|F-M\|_2^2$, so the $d_2$ Fréchet mean is the $\mathbf F$-matrix closest to $M$ in Euclidean norm.

**Theorem (Kingman/Yule shape).** Let $F$ be the $\mathbf F$-matrix of a ranked tree shape drawn from the Kingman coalescent, equivalently the Yule model or the Blum–François $\beta$-splitting model with $\beta=0$. This law assigns a shape with $c$ cherries the probability $2^{n-1-c}/(n-1)!$. Then for $1\le j\le i\le n-1$:

1. the distribution of the $i$-th row of $F$ does not depend on $n$;
2. $\displaystyle \mathbb E[F_{ij}]=\frac{j(j+1)}{i}$;
3. for $i\ge2$, $\displaystyle \operatorname{Var}[F_{ij}]=\frac{j^2(j+1)^2}{i^2(i-1)}+\frac{j(j+1)(i-2j-1)}{i(i-1)}$.

The variance formula vanishes on the deterministic diagonal and subdiagonal. For example, for $i=3,j=1$ it gives $2/9$, the variance of a Bernoulli$(2/3)$ entry.

**Corollaries.**
- *(Central limit theorem.)* For i.i.d. $F^1,\dots,F^m\sim P$ on $\mathcal F_n$ with entrywise sample mean $\bar F_m$, we have $\sqrt m(\bar F_m-M)\Rightarrow N(0,\Sigma)$ with $\Sigma_{ij,kl}=\operatorname{Cov}_P[F_{ij},F_{kl}]$. If $\Sigma$ is invertible, the empirical covariance $\hat\Sigma$ gives $\hat\Sigma^{-1/2}\sqrt m(\bar F_m-M)\Rightarrow N(0,I)$.
- *(Ranked genealogies.)* If tree topology and branching times are independent, as in neutral isochronous coalescents with variable population size, the $d_2$ Fréchet mean genealogy is obtained by optimizing the topology and the time vector separately.
- *(Extremal shapes.)* The ranked tree shape at maximal $d_1$ and $d_2$ distance from the caterpillar has $F^{(\mathrm{bal})}_{i,j}=\max\{0,2j-i+1\}$ for $1\le j\le i\le n-1$.

## Depends on

- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)
- [Ranked labeled history](../ranked-history.md)
- [F-matrix encoding and metrics on ranked tree shapes](../f-matrix-distances-between-ranked-tree-shapes/f-matrix-encoding-and-metrics-on-ranked-tree-shapes.md)

## Proof depends on

- [Multivariate central limit theorem](../../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/tendsto-in-distribution-inv-sqrt-smul-su.md)

## Expansion

Under the Kingman coalescent, going forward in time from the root, each of the $i$ lineages present is equally likely to split next. Row $i$ of $F$ is therefore a function of the first $i$ splits of a Pólya-urn–like process, so it does not depend on $n$. Each $F_{ij}$ is a sum of indicators that a given lineage extant in $I_j$ survives unsplit through intervals $j+1,\dots,i$. The probability of surviving one step from $k$ to $k+1$ lineages is $(k-1)/k$. Telescoping these factors gives $\mathbb E F_{ij}=(j+1)\prod_{k=j+1}^{i}\frac{k-1}{k}=\frac{j(j+1)}{i}$, and pairwise survival probabilities give the second moments. The source (Theorem 8.4 of the preprint) also gives closed formulas for the covariances $\operatorname{Cov}[F_{i_1j_1},F_{i_2j_2}]$, in four cases according to the relative order of the indices; they are not part of the statement above. Because $M$ is known in closed form for $\beta=0$, the Fréchet mean can be computed by mixed-integer programming or simulated annealing over $\mathcal F_n$ near $M$, without enumerating $\mathcal F_n$.

The statements are, in the source, the F-matrix bijection theorem (Section 2), the separation proposition for genealogies (Section 3.1), the balanced-tree proposition (Section 4), and the Kingman F-matrix theorem with the CLT theorem and corollary (Section 5.2), with proofs in the appendices.

## Sources

- S. Rajanala, J. A. Palacios, "Statistical summaries of unlabelled evolutionary trees", *Biometrika* 111 (2024), 171–193, <https://doi.org/10.1093/biomet/asad025>; preprint "Statistical summaries of unlabelled evolutionary trees and ranked hierarchical clustering trees", arXiv:2106.02724 (2021), <https://doi.org/10.48550/arXiv.2106.02724> (the section numbers above are the preprint's).
