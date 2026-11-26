# Reproduction numbers of an influenza–pneumococcal carriage model

**Model.** Hosts are classified by viral (influenza) status $a\in\{S,I,R\}$ and bacterial (pneumococcal) status $b\in\{S,C,I,R\}$, giving twelve compartments $X_{ab}$ with recruitment $\Lambda$ and natural death $\mu$. Influenza follows SIRS dynamics (transmission $\beta$, recovery $\gamma$, waning $\iota$) independent of bacterial status. Pneumococcus is transmitted by asymptomatic carriers (rate $\beta_c$) and actively infected hosts (rate $\beta_I$); carriers progress to active disease at a rate $\kappa_a$ that depends on viral status, or clear carriage at rate $\theta$; active infections recover at rate $\gamma_b$ and immunity wanes at rate $\iota_b$. The region $\{\sum_{a,b}X_{ab}\le\Lambda/\mu\}$ is compact, positively invariant and attracting.

In proportions, the virus-free bacterial subsystem is
$$x_{ss}'=\mu-(\beta_cx_{sc}+\beta_Ix_{si})x_{ss}+\iota_bx_{sr}-\mu x_{ss},\qquad x_{sc}'=(\beta_cx_{sc}+\beta_Ix_{si})x_{ss}-j_1x_{sc},$$
$$x_{si}'=\kappa_Sx_{sc}-j_2x_{si},\qquad x_{sr}'=\gamma_bx_{si}+\theta x_{sc}-j_3x_{sr},$$
with $j_1=\kappa_S+\theta+\mu$, $j_2=\gamma_b+\mu$, $j_3=\iota_b+\mu$, and let $j_4=\gamma+\mu$.

**Reproduction numbers.** By the next-generation method,
$$\mathcal R_{0a}^{V}=\frac{\beta}{j_4},\qquad \mathcal R_{0b}^{T}=\frac{\beta_cj_2+\beta_I\kappa_S}{j_1j_2}=\frac{\beta_c}{j_1}+\frac{\kappa_S}{j_1}\cdot\frac{\beta_I}{j_2},\qquad \mathcal R_0=\max\{\mathcal R_{0a}^{V},\mathcal R_{0b}^{T}\}.$$
The bacterial number adds infections caused during carriage to those caused after progression to active disease (weighted by the progression probability $\kappa_S/j_1$). The disease-free equilibrium is locally asymptotically stable iff $\mathcal R_0<1$. The virus-free subsystem has a unique endemic equilibrium iff $\mathcal R_{0b}^{T}>1$, and the bacteria-free (influenza-only) subsystem has a forward (supercritical) bifurcation at $\mathcal R_{0a}^{V}=1$. Invasion reproduction numbers measure each pathogen's ability to invade when the other is endemic.

## Expansion

Only the carrier and actively infected bacterial classes and the viral-infected classes generate new infections near the disease-free state, so $FV^{-1}$ has two nonzero rows and its spectral radius is the larger of the two single-pathogen numbers. The source paper also states a backward bifurcation of the bacterial subsystem at $\mathcal R_{0b}^{T}=1$ when $\beta_c>\kappa_S+\theta+\mu$. Since $\mathcal R_{0b}^{T}\ge\beta_c/j_1$, that condition forces $\mathcal R_{0b}^{T}>1$, so it cannot hold at the bifurcation point; this claim is therefore left out here.

## Sources

- Anna Daniel Fome, Wolfgang Bock, Thomas Götz, "When Reducing Transmission Is Not Enough: Carrier Dynamics and Backward Bifurcation in Influenza-Pneumococcal Co-infection", arXiv:2610.09978 (2026), Section 2 (model, Theorem 3), Section 3 (reproduction numbers) and Section 4 (Theorem 7, virus-free equilibrium lemma), <https://doi.org/10.48550/arXiv.2610.09978>.
