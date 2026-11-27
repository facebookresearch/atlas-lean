# Expected robustness of a bipartite stochastic block model and its density bound

**Setting.** A bipartite interaction network between $n_r$ row species and $n_c$ column species, such as plants and pollinators or hosts and parasites, is an incidence matrix $A\in\{0,1\}^{n_r\times n_c}$. Row species go extinct one by one in the order of a permutation $s$ (*primary extinctions*). A column species goes extinct (*secondary extinction*) once all its row partners have disappeared. After $m$ primary extinctions, the surviving fraction of column species is

$$R(A,s,m)=1-\frac1{n_c}\sum_{j=1}^{n_c}\mathbf 1\Big\{\sum_{i=m+1}^{n_r}A_{s(i)j}=0\Big\}.$$

The **robustness function** is $R_{\mathbb S}(A,m)=\mathbb E_{S\sim\mathbb S}[R(A,S,m)]$ for an extinction-order distribution $\mathbb S$. The **robustness statistic** is the normalized area under it, $\overline R_{\mathbb S}(A)=\frac1{n_r}\sum_{m=0}^{n_r}R_{\mathbb S}(A,m)$.

**Model.** In a bipartite stochastic block model $\mathrm{biSBM}(\theta,n)$, row species are assigned independently to blocks $k\in\{1,\dots,Q_r\}$ with probabilities $\pi_k$, and column species to blocks $q\in\{1,\dots,Q_c\}$ with probabilities $\rho_q$. Given the blocks, $A_{ij}\sim\mathrm{Bernoulli}(\delta_{kq})$ independently. Write $\delta_{+q}=\sum_k\pi_k\delta_{kq}$ for the mean connectivity of column block $q$, and $d=\sum_{k,q}\pi_k\delta_{kq}\rho_q$ for the expected density.

**Theorem.**

1. *(Uniform extinction order.)* If $S$ is uniform on permutations, independent of $A$, then for $m=0,\dots,n_r$

$$R_{\theta,n,\mathbb U}(m)=1-\sum_{q=1}^{Q_c}\rho_q\,(1-\delta_{+q})^{n_r-m},\qquad \overline R_{\theta,n,\mathbb U}=\frac1{n_r}\sum_{m=0}^{n_r}\Big[1-\sum_{q}\rho_q(1-\delta_{+q})^{n_r-m}\Big].$$

In particular the expected robustness depends on the row structure only through the column-block mean connectivities $\delta_{+q}$.
2. *(Block-ordered extinction.)* If row blocks go extinct in the order $1,2,\dots,Q_r$, uniformly within each block, then

$$R_{\theta,n,\mathbb B}(m)=1-\sum_{q=1}^{Q_c}\rho_q\sum_{n_1+\dots+n_{Q_r}=n_r}\binom{n_r}{n_1,\dots,n_{Q_r}}\prod_{k=1}^{Q_r}\pi_k^{n_k}(1-\delta_{kq})^{\min^+(n_k,\ \sum_{l\le k}n_l-m)},$$

with $\min^+(x,y)=\max(0,\min(x,y))$.
3. *(Density bound.)* Under uniform extinction, for every $m$, $R_{\theta,n,\mathbb U}(m)\le1-(1-d)^{n_r-m}$. For $m\le n_r-2$, the maximum over all parameters with expected density $d$ is attained exactly when all column blocks have the same mean connectivity, $\delta_{+q}=\delta_{+q'}$ for all $q,q'$. This includes the bipartite Erdős–Rényi network.
4. *(Variance.)* The variance over $A$ of $R_{\mathbb U}(A,m)$ is given explicitly in terms of $\eta_q=1-\delta_{+q}$ and $\eta_{qq'}=\sum_k\pi_k(1-\delta_{kq})(1-\delta_{kq'})$, through hypergeometric weights $\binom{m}{l-m}\binom{n_r-m}{l-m}/\binom{n_r}{m}$. It splits into a $1/n_c$ within-column term and an $(n_c-1)/n_c$ term that comes from correlations between columns sharing row partners.

So at fixed density, heterogeneity in how column groups connect, such as specialist versus generalist column blocks, can only lower expected robustness under random extinctions. Modular or nested row structure matters only through its effect on the $\delta_{+q}$ and on the extinction order.

## Expansion

Under uniform extinction, a column species $j$ in block $q$ survives $m$ primary extinctions iff at least one of the $n_r-m$ surviving rows links to it. Given its block, the surviving rows form a uniform subset of fixed size, and their links to $j$ are independent $\mathrm{Bernoulli}(\delta_{+q})$ after averaging over row blocks. Hence $\mathbb P(\text{extinct})=(1-\delta_{+q})^{n_r-m}$, and averaging over $q$ gives item 1. The bound in item 3 is Jensen's inequality for the convex map $x\mapsto(1-x)^{n_r-m}$ applied to $\delta_{+W}$, where $W\sim\rho$ and $\mathbb E\delta_{+W}=d$. Equality holds iff $\delta_{+W}$ is almost surely constant. Under block-ordered extinction, conditioning on the row block sizes $(n_k)$ shows that after $m$ removals exactly $\min^+(n_k,\sum_{l\le k}n_l-m)$ rows of block $k$ remain, which gives item 2.

These are the expectation and variance propositions of Section 4 and the upper-bound proposition of Section 5.1 of the source.

## Proof depends on

- [Jensen's inequality](../../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Sources

- S.-C. Chabert-Liddell, P. Barbillon, S. Donnet, "Impact of the mesoscale structure of a bipartite ecological interaction network on its robustness through a probabilistic modeling", arXiv:2106.06348 (2021). <https://doi.org/10.48550/arXiv.2106.06348>
