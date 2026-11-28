# Reproduction number of the Ross–Macdonald model with paratransgenic sugar baits

**Model.** Humans ($N$, SIS: susceptible $S_h$, infected $I_h$, recovery rate $\mu$) and mosquitoes ($M = mN$, birth = death rate $\delta$) interact through bites at rate $a$; a fraction $p$ of a mosquito's meals are blood meals and $q = 1 - p$ sugar meals, and $B = xN$ sugar baits carry genetically modified bacteria. A mosquito chooses a human with weight $p$ and a bait with weight $qx$ per human, so blood meals occur at rate $ap/(p + qx)$ per human and bait meals at rate $aqx/(p + qx)$. A bait meal removes a susceptible or exposed mosquito (gametocytes in the midgut, sporozoites not yet in the salivary glands) with probability $\gamma$; removed mosquitoes revert to susceptible at rate $\theta$. Infection probabilities per bite are $b$ (mosquito to human) and $c$ (human to mosquito), and the extrinsic incubation period is a fixed delay $\tau$, survived without death or bacterial removal with probability $e^{-\Lambda\tau}$, $\Lambda = \delta + \frac{a\gamma qx}{p + qx}$. Let

$$r_{df} = \frac{a\gamma qx}{(p + qx)(\delta + \theta) + a\gamma qx}$$

be the disease-free proportion of removed mosquitoes and

$$R_0 = \frac{a^2bcm\,p^2\,(1 - r_{df})\,e^{-\Lambda\tau}}{\delta\mu\,(p + qx)^2}.$$

**Theorem.**

1. (Homogeneous mixing.) If $R_0\le1$, the delay system has a unique equilibrium, the disease-free state $(i_h,i_m,r_m) = (0,0,r_{df})$, and it is stable. If $R_0 > 1$ there is also an endemic equilibrium

$$i_h^\ast = \frac{(R_0 - 1)\delta\mu(p+qx)^2}{(1 - r_{df})\,acp\,e^{-\Lambda\tau}\,(abmp + \mu(p+qx))}, \qquad r_m^\ast = r_{df}(1 - i_m^\ast),$$

where $i_m^\ast$ is the endemic proportion of infected mosquitoes (bait removal acts on susceptible and exposed mosquitoes, the fraction $1 - i_m - r_m$, so $\dot r_m = 0$ gives $r_m = r_{df}(1 - i_m)$; the source's Theorem 1 writes $r_{df}(1 - i_h^\ast)$, a slip), and the disease-free state is unstable. Without baits ($x = 0$) this reduces to the Ross–Macdonald number $a^2bcm\,e^{-\delta\tau}/(\mu\delta)$.
2. (Heterogeneous attractiveness.) If humans in class $i$ have attractiveness $k_i$ (first and second moments $\bar k$, $\hat k$), the disease-free state is stable iff the corresponding $R_0 = \frac{a^2bcm\,p^2\hat k(1 - r_{df})e^{-\zeta\tau}}{\delta\mu(\bar kp + qx)^2}\le1$, where here $r_{df} = \frac{a\gamma qx}{(p\bar k + qx)(\delta + \theta) + a\gamma qx}$ and $\zeta = \delta + a\gamma qx/(p\bar k + qx)$ is the incubation-period hazard; any other equilibrium has $i_h, i_m > 0$.
3. (Targeted baits.) Let the attractiveness values be distinct, $k_i \ne k_j$ for $i \ne j$. If $B_i\le C_i$ baits placed near class $i$ inherit attractiveness $k_i$ and $\sum_iB_i = Nx < \sum_iC_i$, then $R_0$ is strictly decreasing in $y = \sum_ik_iB_i/N$, and the unique allocation minimizing $R_0$ fills the classes greedily in decreasing order of $k_i$ up to their caps.

## Expansion

Baits act on transmission twice: they divert bites ($p^2/(p+qx)^2$, one factor for each direction of transmission), and they remove mosquitoes both before infection (the factor $1 - r_{df}$) and during incubation (the extra hazard in $\Lambda$). Because removed mosquitoes slow the growth of infectious ones, $\partial\dot I_m/\partial R_m\le0$ and the delay system is not cooperative, so the delay cannot be dropped in the linear analysis; instead the characteristic equation $F(\lambda,\tau) = 0$ at the disease-free state is shown to have only roots with negative real part when $R_0 < 1$ (and a zero root with the others stable at $R_0 = 1$), and a positive real root when $R_0 > 1$. For targeted baits, $R_0$ depends on the allocation only through $y$, so minimizing $R_0$ is a linear program in $B_i$ maximizing $\sum_ik_iB_i$ under box and budget constraints, solved by the greedy rule.

## Sources

- Bhushan Kotnis, Joy Kuri, "Evaluating the usefulness of paratransgenesis for malaria control", arXiv (2013). Section 2 (model and symbols), Section 3.1 (reduced delay system, $r_{df}$, $R_0$, Theorem 1), Section 3.2 (Theorem 2), Section 3.3 (targeted bait optimization, Theorem 3). <https://doi.org/10.48550/arXiv.1311.6216>. Published version: Mathematical Biosciences 277 (2016), 117–125, <https://doi.org/10.1016/j.mbs.2016.04.005>; locators above refer to the arXiv version.
