# Boundary equilibria of the two-locus continent–island model

**Model.** A deterministic, continuous-time population of monoecious diploids on an island has two diallelic loci $A$ and $B$. The continent is fixed for $A_2B_2$ and sends migrants at rate $m \ge 0$; the recombination rate is $\rho \ge 0$. Selection is genic (no dominance, no epistasis), with Malthusian parameters $\pm\tfrac12\alpha$ for $A_1/A_2$ and $\pm\tfrac12\beta$ for $B_1/B_2$, and without loss of generality $0 < \alpha \le \beta$. In terms of the island allele frequencies $p$ (of $A_1$), $q$ (of $B_1$) and the linkage disequilibrium $D = x_1x_4 - x_2x_3$,

$$\dot p = \alpha p(1-p) - mp + \beta D, \qquad \dot q = \beta q(1-q) - mq + \alpha D,$$

$$\dot D = [\alpha(1-2p) + \beta(1-2q)]D + m(pq - D) - \rho D,$$

on the region $0 \le p,q \le 1$, $-\min\{pq,(1-p)(1-q)\} \le D \le \min\{p(1-q),(1-p)q\}$.

**Boundary equilibria.**

1. $E_I = (1,1,0)$ (both island alleles fixed) is an equilibrium iff $m = 0$, and then attracts every solution in which both island alleles are initially present.
2. $E_C = (0,0,0)$ (continental haplotype fixed) always exists, with eigenvalues $\alpha - m$, $\beta - m$, $\alpha + \beta - \rho - m$. It is asymptotically stable iff $m > \max(\beta, m_C)$ with $m_C = \alpha + \beta - \rho$, and globally asymptotically stable whenever $m \ge \alpha + \beta$.
3. For $0 < m < \alpha$, $E_A$: $\hat p = 1 - m/\alpha$, $\hat q = 0$, $\hat D = 0$. It attracts its one-locus edge but is always unstable in the two-locus system.
4. For $0 < m < \beta$, $E_B$: $\hat p = 0$, $\hat q = 1 - m/\beta$, $\hat D = 0$. Its eigenvalues are real, and $E_B$ is asymptotically stable iff $m_B < m < \beta$, where

$$m_B = \alpha\left(1 + \frac{\beta - \alpha}{\rho}\right);$$

the stability window is non-empty iff $\alpha < \min(\rho,\beta)$.
5. If $\rho = 0$ and $0 < m < \alpha+\beta$, the equilibrium $E_0$ with only $A_1B_1$ and $A_2B_2$ present, $\hat p = \hat q = 1 - \frac{m}{\alpha+\beta}$, $\hat D = \frac{m}{\alpha+\beta}\left(1 - \frac{m}{\alpha+\beta}\right)$, is asymptotically stable with eigenvalues $-\alpha$, $-\beta$, $m - \alpha - \beta$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For $E_B$ the non-trivial eigenvalues are $\lambda^B_\pm = \tfrac12\big(2\alpha - \beta - \rho \pm \sqrt{(\beta+\rho)^2 - 4m\rho}\big)$ together with $m - \beta$; $\lambda^B_- < 0$ always, and solving $\lambda^B_+ = 0$ gives $4m\rho = (\beta+\rho)^2 - (\beta+\rho-2\alpha)^2$, i.e. $m = m_B$. The analogous eigenvalues of $E_A$ satisfy $\lambda^A_+ > 0$ because the locus under weaker selection cannot hold its island allele against a fixed continental allele at the stronger locus. With tight linkage the island haplotype behaves like a single allele of selective advantage $\alpha+\beta$, which is why $E_0$ survives up to $m = \alpha+\beta$, the classical one-locus threshold for that combined advantage. At $m = 0$, mean fitness $\bar w = \alpha(2p-1) + \beta(2q-1)$ is a Lyapunov function, giving global convergence to $E_I$.

## Sources

- R. Bürger, A. Akerman, "The effects of linkage and gene flow on local adaptation: a two-locus continent–island model", Theoretical Population Biology 80(4) (2011) 272–288, Eqs. (2.5), (3.2)–(3.14) and Section 3.4, <https://doi.org/10.1016/j.tpb.2011.07.002>, PMCID PMC3257863.
