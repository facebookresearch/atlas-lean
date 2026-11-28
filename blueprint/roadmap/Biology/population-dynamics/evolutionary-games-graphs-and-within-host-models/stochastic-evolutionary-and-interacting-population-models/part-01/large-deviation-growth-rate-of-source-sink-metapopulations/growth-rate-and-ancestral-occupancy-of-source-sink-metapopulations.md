# Growth rate and ancestral occupancy frequencies of a source–sink metapopulation

**Model.** A species lives on $K$ habitat patches with discrete, non-overlapping generations and no density dependence. Each individual in patch $i$ independently leaves a random number $N_i$ of offspring with mean $m_i=\mathbb E N_i>0$ and $\mathbb E(N_i\log^+N_i)<\infty$; each offspring then disperses independently from patch $i$ to patch $j$ with probability $d_{ij}$, where the stochastic dispersal matrix $D=(d_{ij})$ is irreducible and aperiodic. Patches with $m_i>1$ are sources and those with $m_i\le1$ sinks. The **random disperser** is the Markov chain on patches with transition matrix $D$, with stationary distribution $u$. Let $\rho$ be its growth rate, the Perron root of the mean matrix $A=(m_id_{ij})$, so that the population grows like $\rho^n$ on survival. On the simplex $\mathcal F=\{f\in\mathbb R^K_{\ge0}:\sum_if_i=1\}$ of occupancy frequencies define the **reward** and the Donsker–Varadhan **rate function** of the random disperser

$$R(f)=\sum_{i=1}^Kf_i\log m_i,\qquad I(f)=\sup_{v\gg0}\sum_{i=1}^Kf_i\log\frac{v_i}{(vD)_i}.$$

**Theorem.**

1. $\displaystyle\log\rho=\max_{f\in\mathcal F}\bigl\{R(f)-I(f)\bigr\}.$
2. If $\rho>1$, then conditionally on survival up to time $n$, the fraction of generations that the ancestral line of a uniformly chosen individual alive at time $n$ spent in patch $i$ converges in probability to $\varphi_i$, where $\varphi\in\mathcal F$ is the unique maximizer: $\log\rho=R(\varphi)-I(\varphi)$. (Theorem 4.1 of the source prints this clause "if ρ > 0", which holds for every metapopulation since all $m_i>0$; its proof in Appendix A uses $Z_n\sim W\rho^n$ with a non-degenerate limit $W$, which requires the supercritical case $\rho>1$, so the page states the clause for $\rho>1$.)
3. $\varphi$ equals the stationary distribution $u$ of the random disperser if and only if $m_1=\dots=m_K$; otherwise ancestral lines of survivors over-occupy source patches relative to a typical disperser.

The formula decouples demography ($R$) from dispersal ($I$): the growth rate is the best trade-off between the fitness payoff of occupying good patches and the large-deviation cost for a random walk of occupying them with atypical frequencies. Analogous formulas hold in periodic or random (Markovian) environments, with the rate function of the joint patch–environment chain, and they show that two time-averaged sinks can jointly allow survival.

## Expansion

By the many-to-one formula, $\mathbb E Z_n=\mathbb E\bigl(\prod_{k<n}m_{X_k}\bigr)=\mathbb E\exp\bigl(n\,R(L_n)\bigr)$, where $L_n$ is the empirical occupation measure of the random disperser. Sanov's theorem for the empirical measure of an irreducible finite Markov chain (Donsker–Varadhan) gives $\mathbb P(L_n\approx f)\approx e^{-nI(f)}$, so Varadhan's lemma yields $\frac1n\log\mathbb EZ_n\to\max_f\{R(f)-I(f)\}$; since $\mathbb EZ_n$ grows like $\rho^n$, this is $\log\rho$. Strict concavity of $R-I$ (from the strict convexity of $I$ on the relevant face) gives uniqueness of $\varphi$, and the same tilting argument, combined with the $L\log L$ condition (which makes $Z_n/\rho^n$ converge to a non-degenerate limit), shows that the ancestral line of a typical survivor behaves like the disperser tilted by $e^{nR(L_n)}$, whose occupation frequencies concentrate at $\varphi$. Equality $\varphi=u$ forces $\nabla R$ to be constant on $\mathcal F$, i.e. all $m_i$ equal.

## Sources

- Vincent Bansaye, Amaury Lambert, "New approaches of source-sink metapopulations decoupling the roles of demography and dispersal", arXiv (2012). Section 4 (definitions of $\mathcal F$, $R$, $I$; Theorem 4.1), Section 5 (fluctuating environments, Theorems 5.1–5.3), Section 8 (proof of Theorem 4.1). <https://doi.org/10.48550/arXiv.1210.4641>. Published version: "New approaches to source–sink metapopulations decoupling demography and dispersal", Theoretical Population Biology 88 (2013), 31–46, <https://doi.org/10.1016/j.tpb.2013.06.003>; locators above refer to the arXiv version.
