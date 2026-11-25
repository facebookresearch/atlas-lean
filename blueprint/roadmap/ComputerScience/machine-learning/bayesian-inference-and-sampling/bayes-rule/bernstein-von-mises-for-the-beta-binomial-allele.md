# Bernstein–von Mises for the Beta–Binomial allele-frequency posterior

Let $a,b>0$ and $0<p_0<1$. For $M\ge1$ let $K_M\sim\mathrm{Bin}(M,p_0)$, and give the allele frequency $p$ the prior $\mathrm{Beta}(a,b)$, so that by [Bayes' rule](posterior-eq-bayes-posterior.md) the posterior of $p$ given $K_M$ is $\mathrm{Beta}(a+K_M,\ b+M-K_M)$. Then

$$d_{\mathrm{TV}}\Bigl(\mathrm{Beta}(a+K_M,\ b+M-K_M),\ \mathcal N\Bigl(\frac{K_M}{M},\ \frac{p_0(1-p_0)}{M}\Bigr)\Bigr)\ \xrightarrow{\ P\ }\ 0\qquad(M\to\infty),$$

where $d_{\mathrm{TV}}$ is the total-variation distance. This is a closed-form special case of the Bernstein–von Mises theorem; the general theorem for regular parametric models is a separate statement.

The posterior mean is within $O(1/M)$ of $K_M/M$ deterministically:

$$\Bigl|\frac{a+K_M}{a+b+M}-\frac{K_M}{M}\Bigr|=\frac{|aM-(a+b)K_M|}{M(a+b+M)}\le\frac{a+b}{M}.$$

The interior hypothesis cannot be dropped: if $p_0\in\{0,1\}$, then $K_M=Mp_0$ almost surely, the displayed normal law is the point mass at $p_0$, and its total-variation distance from the absolutely continuous posterior is $1$ for every $M$.

## Depends on

- [Bayes' rule for discrete observations](posterior-eq-bayes-posterior.md)

## Proof depends on

- [Prokhorov's theorem, sequential form on $\mathbb{R}$](../../../../Probability/convergence-of-measures/prokhorov-theorem/prokhorov-sequential.md)

## Expansion

A full proof compares the Beta density with the normal density after centring at $K_M/M$ and scaling by $\sqrt M$: Stirling's formula for the normalizing constant, a second-order expansion of $(a+K-1)\log p+(b+M-K-1)\log(1-p)$ around $K/M$, and tail bounds, together with $K_M/M\to p_0$ in probability, which turns the variance $\frac{K_M}{M}(1-\frac{K_M}{M})/M$ into $p_0(1-p_0)/M$ at a cost that vanishes in total variation. The variance $p_0(1-p_0)/M$ is the inverse Fisher information of $M$ Bernoulli draws.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., 2002, Bayesian asymptotics (topic citation).
