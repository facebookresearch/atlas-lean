# Calibrating vivax transmission from observed incidence

**Model.** Population proportions are split by blood-stage infection ($I$ infected, $S$ not) and liver-stage carriage ($L$ with hypnozoites, $0$ without): $I_L,I_0,S_L,S_0$, with $I=I_L+I_0$. Infections arise at rate $\lambda I+\delta$ ($\lambda$ transmission rate, $\delta$ importation), relapses at rate $f$, blood-stage clearance at rate $r$ and liver-stage clearance at rate $\gamma_L$. A proportion $\alpha$ of new infections is effectively treated, of which a proportion $\beta$ also receives radical cure. For instance

$$\dot I_0=-(\lambda I+\delta)I_0+\gamma_LI_L-rI_0,\qquad \dot I=(1-\alpha)(\lambda I+\delta)(1-I)+(1-\alpha)fS_L-rI .$$

Without importation, the reproduction numbers without and with control are

$$R_0=\frac{\lambda(\gamma_L+f)(\gamma_L+r)}{r\gamma_L(f+\gamma_L+r)}=\frac\lambda r+\frac{\lambda f}{\gamma_L(f+\gamma_L+r)},\qquad R_c=\frac{\lambda(1-\alpha)(\gamma_L+r)(f+\gamma_L)}{r\bigl[\gamma_L(f+\gamma_L+r)+\alpha f\bigl(\beta(r+\gamma_L)-\gamma_L\bigr)\bigr]}.$$

**Calibration.** Let $h$ be the observed incidence of treated cases, $\rho$ the observation rate and $p$ the observed proportion of imported cases. At equilibrium,

$$I^*=\frac{h(1-\alpha)}{\rho r},\qquad \delta=\frac{ph}{\rho(1-I^*)},$$

and eliminating $S_L^*$ and $I_L^*$ from the equilibrium equations shows that $\lambda$ solves a cubic equation $P(\lambda)=0$ whose coefficients are explicit in $I^*,\delta,r,f,\gamma_L,\alpha,\beta$; its leading coefficient is $I^{*3}(1-I^*)>0$.

**Theorem.** If $h>0$, $r>0$ and $\alpha<1$, then $P$ has at most one positive real root, and it has two nonnegative roots (one being $0$) only if $\alpha\beta=\gamma_L=\delta=0$. Hence, whenever the observed data are compatible with the model, the transmission rate $\lambda$ consistent with the observed incidence and importation is unique and can be found numerically.

## Expansion

The equilibrium of $\dot I=0$ gives $h=r\rho I^*/(1-\alpha)$, hence $I^*$; writing the imported part of observed incidence as $ph=\rho\delta(1-I^*)$ gives $\delta$. Solving the $I_0$ and $S_L$ equilibrium equations for $I_L^*$ and $S_L^*$ and substituting into $\dot I=0$ yields a polynomial identity of degree three in $\lambda$. Uniqueness of the positive root is proved in Appendix A of the paper from the signs of the coefficients. The paper also derives validity conditions under which no positive root exists, for instance when the observed imported proportion is too high for the observed incidence; in those cases the data are inconsistent with the model assumptions.

## Sources

- C. Champagne, M. Gerhards, J. Lana, B. García Espinosa, C. Bradley, O. González, J. M. Cohen, A. Le Menach, M. T. White, E. Pothin, "Using observed incidence to calibrate the transmission level of a mathematical model for *Plasmodium vivax* dynamics including case management and importation", Mathematical Biosciences 343 (2022) 108750, <https://doi.org/10.1016/j.mbs.2021.108750>, PMCID PMC8786669. Eqs. (1)–(17) and Theorem 1.
