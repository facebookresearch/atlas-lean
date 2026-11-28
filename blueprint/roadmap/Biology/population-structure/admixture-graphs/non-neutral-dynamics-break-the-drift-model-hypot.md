# Genic selection breaks the uncorrelated-increment hypothesis of the drift model

Consider one biallelic locus and haploid Wright–Fisher reproduction with genic selection: a population with allele frequency $p$ produces the next generation's frequency $\mathrm{Bin}(M,\varphi_s(p))/M$, where $M\ge1$ is the number of gene copies, $s>-1$ is the selection coefficient and

$$\varphi_s(p)=\frac{(1+s)p}{1+sp}.$$

Take two consecutive edges root $\to X\to A$ of a population tree, each consisting of one generation of this update with fresh randomness, and a deterministic root frequency $r=p_0\in[0,1]$. Let $\delta_1=p_X-r$ and $\delta_2=p_A-p_X$ be the drift increments along the two edges. Then

$$\mathbb E[\delta_1\delta_2]=\mathbb E\!\left[(p_X-r)\,\frac{s\,p_X(1-p_X)}{1+s\,p_X}\right].$$

For $s=0$ this is $0$, as the [admixture-graph drift model](../patterson-s-f-statistics/drift-model.md) requires. For $M=2$, $r=\frac14$ and $s=\frac1{10}$,

$$\mathbb E[\delta_1\delta_2]=\frac{55}{23534}\ne0,\qquad \operatorname{Cov}(\delta_1,\delta_2)=\frac{1045}{482447}\ne0 .$$

Hence, under selection, the drift increments of distinct edges can be correlated, and for these parameters the hypothesis $\int\delta_e\delta_f\,d\mu=0$ ($e\ne f$) of the drift model fails, whereas [neutral Wright–Fisher on an admixture graph realizes the drift model](neutral-wright-fisher-on-an-admixture-graph-real.md). Quantitative bias laws for $f_3$- and $f_4$-statistics under weak or linked selection are outside this statement.

## Depends on

- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)

## Proof depends on

- [A pulse followed by binomial resampling realizes the drift model](neutral-wright-fisher-on-an-admixture-graph-real.md)
- [Martingale problem for the Wright–Fisher diffusion](../../population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md), for a diffusion-scale analogue of the computation

## Expansion

A full proof page must establish the following.

- The conditional mean $\mathbb E[p_A\mid p_X]=\varphi_s(p_X)$ and $\varphi_s(x)-x=s\,x(1-x)/(1+sx)$, which give the displayed formula by conditioning on $p_X$.
- The exact example: $\varphi_{1/10}(\frac14)=\frac{11}{41}$, so $p_X=\frac12$ with probability $2\cdot\frac{11}{41}\cdot\frac{30}{41}=\frac{660}{1681}$, while $p_X\in\{0,1\}$ contributes nothing; with $\varphi_{1/10}(\frac12)-\frac12=\frac1{42}$ this gives $\frac{660}{1681}\cdot\frac14\cdot\frac1{42}=\frac{55}{23534}$. With $\mathbb E\delta_1=\frac3{164}$ and $\mathbb E\delta_2=\frac{110}{11767}$ the covariance is $\frac{1045}{482447}$.
- The role of the root: with $r=\frac12$ and $M=2$ the uncentred cross moment vanishes for every $s$, although the covariance does not ($-\frac{55}{194481}$ at $s=\frac1{10}$), so the example must fix $r$.
- Why neutrality matters: under neutrality the frequency process is a martingale with independent update randomness, which is exactly what makes increments on distinct edges orthogonal.

## Sources

- B. M. Peter, *Admixture, population structure, and F-statistics*, Genetics 202(4) (2016), 1485–1501, doi:10.1534/genetics.115.183913, <https://pmc.ncbi.nlm.nih.gov/articles/PMC4905545/> (background: orthogonality of drift on distinct edges holds for any model in which the expected allele frequency is the current one and increments are independent). The exact example is a local computation in rational arithmetic.
