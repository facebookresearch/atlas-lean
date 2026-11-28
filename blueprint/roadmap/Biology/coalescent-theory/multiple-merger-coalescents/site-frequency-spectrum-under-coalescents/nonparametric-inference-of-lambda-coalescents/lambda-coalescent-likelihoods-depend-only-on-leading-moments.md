# Lambda-coalescent likelihoods depend only on leading moments

**Setting.** For a $\Lambda$-coalescent with recurrent mutation on $d$ types, let $\mathbf P^\Lambda_n(\mathbf n)$ be the probability of observing type counts $\mathbf n$ in a sample of size $n$, and let $\lambda_k=\int_{[0,1]}r^{k-2}\Lambda(dr)$ ($k\ge2$, with $\lambda_2=1$ for a probability measure) be the moments of $\Lambda$ that drive the merger rates $\lambda_{p,k}=\int(1-r)^{p-k}r^{k-2}\Lambda(dr)$.

**Lemma (moment sufficiency).** For a probability measure $\Lambda$ on $[0,1]$, $\mathbf P^\Lambda_n(\mathbf n)$ depends on $\Lambda$ only through $(\lambda_3,\lambda_4,\dots,\lambda_n)$: any two probability measures whose moments $\lambda_3,\dots,\lambda_n$ agree give identical likelihoods for every data set of size $n$. (For a finite measure of arbitrary total mass the likelihood depends on $(\lambda_2,\dots,\lambda_n)$; $\lambda_2=\Lambda([0,1])$ is a time scale.)

**Theorem (severe non-identifiability).** For every $n\ge3$ and every sequence $(\lambda_k)_{k=3}^n$ in the interior of the set of moment sequences $\big(\int x^{k-2}\Lambda(dx)\big)_{k=3}^n$ of probability measures $\Lambda$ on $[0,1]$, there are uncountably many probability measures $\Lambda$ with these moments, all satisfying the sharp Chebyshev–Markov–Stieltjes inequalities, such that any two of them are mutually singular: $d_{TV}(\Lambda_x,\Lambda_y)=2$. The source states this "for any $n \in \mathbb N$ and any completely monotonic sequence of moments $\{\lambda_{k,k}\}_{k=3}^n$ with $\lambda_{3,3}\le1$" (Theorem 3). The page differs because the claim fails for sequences on the boundary of the moment set, whose representing measure is unique: $\lambda_3=1$ forces $\Lambda=\delta_1$, and $\lambda_3=0$ forces $\Lambda=\delta_0$.

**Optimization over moment classes.** Fix $m$ linear moment constraints: constants $c_1,\dots,c_m\in\mathbb R$, indices $i_1,\dots,i_m\in\{3,\dots,n\}$ and signs $j_1,\dots,j_m\in\{0,1\}$, and let $\mathcal C_m$ be the set of probability measures $\Lambda$ on $[0,1]$ with $(-1)^{j_k}\lambda_{i_k}\le c_k$ for $k=1,\dots,m$. For a functional $F(\Lambda)=\mathbb E_\Lambda[q]$ with $q$ bounded on one side (more generally any measure-affine $F$), its infimum and supremum over $\mathcal C_m$ coincide with the infimum and supremum over the members of $\mathcal C_m$ that are discrete with at most $m+1$ atoms. Taking $\mathcal C_m$ to enclose a credible region of a posterior over truncated moment sequences makes credible bounds for such functionals computable by finite-dimensional optimization.

## Expansion

Every merger rate is a linear combination of moments: expanding $(1-r)^{p-k}$ shows $\lambda_{p,k}$ is a finite alternating sum of $\lambda_k,\dots,\lambda_p$, and a sample of size $n$ never has more than $n$ blocks, so only moments up to order $n-2$ in $r$ enter the recursion for $\mathbf P^\Lambda_n$. Classical moment theory then shows a finite moment sequence leaves a huge set of compatible measures, including mutually singular ones, so data can only ever constrain truncated moments. Measure-affine functionals are extremized at extreme points of the moment class, which are finitely-atomic measures (Winkler-type results), yielding a finite-dimensional optimization; a pseudo-marginal Metropolis–Hastings sampler handles the posterior on moments.

## Depends on

- [Posterior consistency for Lambda-measures from time-series data](posterior-consistency-for-lambda-measures-from-time-series-data.md)

## Sources

- Jere Koskela, Paul A. Jenkins and Dario Spanò, "Bayesian non-parametric inference for $\Lambda$-coalescents: Posterior consistency and a parametric method", *Bernoulli* 24(3) (2018), 2122–2153. <https://doi.org/10.3150/16-BEJ923>
- Preprint version (the locators in this item follow its numbering): Jere Koskela, Paul A. Jenkins, Dario Spanò, "Bayesian non-parametric inference for $\Lambda$-coalescents: consistency and a parametric method", arXiv:1512.00982: Lemma 4 (likelihood depends on $\lambda_3,\dots,\lambda_n$), Lemma 5 (Chebyshev–Markov–Stieltjes inequalities), Theorem 3 (mutually singular measures with equal moments), Lemmas 6–7 (measure-affine functionals and finitely-atomic optimizers). <https://doi.org/10.48550/arXiv.1512.00982>
