# Profiling the admixture proportions in the qpGraph fit

Fix finite statistic and edge sets $I,E$, a finite number $k$ of admixture parameters, estimated statistics $f\in\mathbb R^I$, a symmetric positive definite covariance matrix $Q$, and $L_{\max}>0$. For $\alpha\in[0,1]^k$, let $B(\alpha)$ be an $I\times E$ real matrix with polynomial entries. Restrict lengths to the fixed, nonempty compact box $K=[0,L_{\max}]^E$, independent of $\alpha$. Then the profiled qpGraph score is continuous and has an attained global maximum on the parameter box.

## Compact profile and attainment

Using the [score](score-s1.md), write

$$H(\alpha,\ell)=S_1(B(\alpha)\ell)=-\frac12(B(\alpha)\ell-f)^{\mathsf T}Q^{-1}(B(\alpha)\ell-f),\qquad\varphi_K(\alpha)=\max_{\ell\in K}H(\alpha,\ell).$$

The function $H$ is continuous, hence uniformly continuous on the compact product $[0,1]^k\times K$. Its maximum over $K$ exists for each $\alpha$, and

$$|\varphi_K(\alpha)-\varphi_K(\beta)|\le\max_{\ell\in K}|H(\alpha,\ell)-H(\beta,\ell)|.$$

To see the inequality, bound $H(\alpha,\ell)$ by $H(\beta,\ell)$ plus the displayed maximum, maximize over the same set $K$, and interchange $\alpha,\beta$. Uniform continuity makes the right-hand side tend to zero as $\beta\to\alpha$. Thus $\varphi_K$ is continuous, attains its maximum on $[0,1]^k$, and an inner maximizer gives a pair $(\alpha_*,\ell_*)$ attaining the joint maximum of $H$. The argument also works for any fixed nonempty compact feasible set and continuous $B$; no full-rank assumption is needed. Empty coordinate sets cause no exception, since their products are singletons.

## Why the length bound matters

For each fixed $\alpha$, a maximizer over **all** nonnegative lengths [exists](exists-is-constrained-maximizer.md). Pointwise existence does not imply continuity of that unbounded profile. With one statistic and edge, $B(\alpha)=\alpha^2$, $f=Q=1$, and $\alpha\in[0,1]$,

$$\max_{\ell\ge0}-\frac12(\alpha^2\ell-1)^2=\begin{cases}0,&\alpha>0,\\-1/2,&\alpha=0.\end{cases}$$

For $\alpha>0$ the maximizer $\ell=\alpha^{-2}$ escapes every bounded set as $\alpha\downarrow0$. At zero every length gives $-1/2$. By contrast, on $[0,L_{\max}]$ the profile is $-\tfrac12\max(1-L_{\max}\alpha^2,0)^2$, a continuous function.

## Distinct optimal proportions

With one statistic, two edges, $B(\alpha)=(\alpha^2,(1-\alpha)^2)$, $f=Q=1$ and $K=[0,2]^2$, set

$$\ell_a=\ell_b=\frac{1}{\alpha^2+(1-\alpha)^2}.$$

For every $\alpha\in[0,1]$, these lengths lie in $[1,2]$ and give prediction $1$, hence the maximal score zero. In particular, the two distinct interior proportions $\alpha=1/4$ and $\alpha=3/4$, both with lengths $(8/5,8/5)$, attain the same maximum within the box. This uses the mixed-drift expression with its third length zero. The existing [mixed-drift level-set theorem](../identifiability-of-admixture-graph-edge-lengths/mixed-drift-eq-mixed-drift-iff.md) keeps $\alpha$ fixed; the explicit witness here, rather than that fixed-$\alpha$ theorem alone, establishes ambiguity across proportions.

Continuity of the optimal value implies neither a unique maximizing proportion nor a unique or continuous choice of maximizing lengths. It also supplies no joint-concavity, algorithmic-global-convergence or statistical-identifiability guarantee. An optimizer returning one maximizing proportion is not evidence that this proportion is identifiable.

## Depends on

- [The qpGraph score S1](score-s1.md)

## Related

- [A constrained maximizer exists for every positive definite covariance](exists-is-constrained-maximizer.md)
- [Level sets of the mixed drift](../identifiability-of-admixture-graph-edge-lengths/mixed-drift-eq-mixed-drift-iff.md)

## Sources

- N. Patterson et al., *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3522152/>, qpGraph, equation (6) and the reduction to optimization over admixture weights.
- R. Maier et al., *On the limits of fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492, <https://reich.hms.harvard.edu/sites/reich.hms.harvard.edu/files/inline-files/elife-85492-v2.pdf>, introduction, for the context of equally fitting models within statistical resolution. The compactness proof and exact algebraic examples above are derived here, not claims quoted from that passage.
