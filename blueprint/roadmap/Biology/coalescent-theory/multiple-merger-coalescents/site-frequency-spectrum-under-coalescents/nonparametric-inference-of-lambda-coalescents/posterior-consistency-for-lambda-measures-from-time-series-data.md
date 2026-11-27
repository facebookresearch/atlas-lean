# Posterior consistency for Lambda-measures from time-series data

**Setting.** A $\Lambda$-coalescent, parametrised by a probability measure $\Lambda$ on $[0,1]$, merges any $k$ of $p$ blocks at rate $\lambda_{p,k}=\Lambda(\{0\})\mathbf 1_{k=2}+\int_{(0,1]}(1-r)^{p-k}r^{k-2}\Lambda(dr)$; it is the genealogy of the $\Lambda$-Fleming–Viot process. Mutations occur at rate $\theta/2$ along lineages with a transition matrix on $d$ types, and the data are type counts $\mathbf n\in\mathbb N^d$ of samples of size $n$. A Bayesian prior $Q$ is placed on $\Lambda$.

**Theorem (contemporaneous data are uninformative).** If the sample is taken at a single time and $\mathbf x=\lim_n\mathbf n/n$ is the limiting relative type frequency vector, then

$$\lim_{n\to\infty}Q(A\mid\mathbf n)=\frac{\int_A\pi^\Lambda(\mathbf x)\,Q(d\Lambda)}{\int\pi^\Lambda(\mathbf x)\,Q(d\Lambda)},$$

where $\pi^\Lambda$ is the stationary density of type frequencies under $\Lambda$. This is positive for every Borel set $A$ meeting the support of $Q$, whatever $\Lambda$ generated the data: no nontrivial prior is consistent.

**Theorem (time series are informative).** Fix $\eta>0$ and let the prior be supported on measures $\Lambda(dr)=\phi(r)dr$ with densities $\phi$ on $[\eta,1]$ bounded above and away from $0$. Observe $m+1$ samples of size $n$ at times $0,\Delta,\dots,m\Delta$ from the stationary process. If, for every $\varepsilon>0$ and data-generating density $\phi_0$, the prior gives positive mass to

$$\Big\{\phi:\int_\eta^1\Big(\Big|\log\frac{\phi_0(r)}{\phi(r)}\Big|+\Big|\frac{\phi_0(r)}{\phi(r)}-1\Big|\Big)r^{-2}\phi_0(r)\,dr<\varepsilon\Big\},$$

then the posterior is weakly consistent: $Q(U^c\mid\mathbf n_0,\dots,\mathbf n_m)\to0$ almost surely as $n,m\to\infty$, for every open neighbourhood $U$ of $\phi_0$.

## Depends on

- [Pitman's merger rate](../../../coalescents/merger-rate.md)

## Expansion

At one time point, the sample reveals (as $n\to\infty$) one draw $\mathbf x$ from the stationary law of the $\Lambda$-Fleming–Viot process, and a single draw cannot identify the generator, so the posterior converges to a nondegenerate reweighting of the prior. In a time series, the frequencies form a Markov chain with transition operator $P^\phi_\Delta$; different $\phi$ give different $P^\phi_\Delta f$ for some test function (identifiability), the operators are uniformly equicontinuous over the prior support, and the Kullback–Leibler-type prior condition then gives consistency by Schwartz-type arguments for ergodic Markov chains. Restricting to $[\eta,1]$ excludes Kingman components and makes the forward process a compound Poisson process with drift.

## Sources

- Jere Koskela, Paul A. Jenkins and Dario Spanò, "Bayesian non-parametric inference for $\Lambda$-coalescents: Posterior consistency and a parametric method", *Bernoulli* 24(3) (2018), 2122–2153. <https://doi.org/10.3150/16-BEJ923>
- Preprint version (the locators in this item follow its numbering): Jere Koskela, Paul A. Jenkins, Dario Spanò, "Bayesian non-parametric inference for $\Lambda$-coalescents: consistency and a parametric method", arXiv:1512.00982: Section 2 (model), Theorem 1 (inconsistency for contemporaneous data), Definitions 1–3 and Lemma 1 (identifiability), Theorem 2 and Lemmas 2–3 (consistency for time series). <https://doi.org/10.48550/arXiv.1512.00982>
