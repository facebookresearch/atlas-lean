# Face-mask threshold for the control reproduction number

For the [quarantine–isolation model with face-mask use](quarantine-isolation-model-with-face-mask-use.md),
write $K_1 = \sigma_u + \alpha_u$, $K_2 = \gamma_u + \phi_u + \delta_u$,
$K_3 = \gamma_h + \nu_h + \delta_h$, $K_4 = \gamma_a + \sigma_a + \delta_a$ and
$K_5 = \gamma_{icu} + \delta_{icu}$, all positive. Let $F$ and $V$ be the next-generation matrices
of new infections and transitions for the infected compartments
$(E_u, E_q, I_u, I_h, I_a, I_{icu})$. The control reproduction number is

$$\mathcal R_c = \rho(F V^{-1}) = \mathcal R_{cu} + \mathcal R_{ca} + \mathcal R_{ch},$$

the sum of contributions of symptomatic, asymptomatic and isolated infectious individuals; for
instance

$$\mathcal R_{cu} = \frac{\beta(1-\epsilon_M c_M)\,p\,(1-q)\, f_1 \sigma_u}{K_1 K_2}.$$

**Theorem.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_c < 1$
and unstable if $\mathcal R_c > 1$.

**Mask threshold.** Every nonzero entry of $F$ carries the factor $\beta(1 - \epsilon_M c_M)$ and
$V$ does not depend on $(\epsilon_M, c_M)$, so
$\mathcal R_c = (1 - \epsilon_M c_M)\,\mathcal R_c^{0}$, where $\mathcal R_c^{0}$ is the value
without masks. Hence if $\mathcal R_c^{0} > 1$, mask use alone makes the disease-free
equilibrium locally asymptotically stable exactly when

$$\epsilon_M c_M \ > \ 1 - \frac{1}{\mathcal R_c^{0}} .$$

## Depends on

- [Quarantine–isolation model with face-mask use](quarantine-isolation-model-with-face-mask-use.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

New infections enter only $E_u$ (fraction $1-q$) and $E_q$ (fraction $q$) at rate
$\beta(1-\epsilon_M c_M)p$ times the weighted infectious prevalence, so $F$ has rank one and
$\rho(FV^{-1})$ is its single nonzero eigenvalue, a sum over the routes through which a new
infection reaches an infectious class. The route $E_u \to I_u$ is taken with probability
$f_1\sigma_u/K_1$ and $I_u$ is occupied for mean time $1/K_2$, which gives $\mathcal R_{cu}$; the
asymptomatic and isolated contributions collect the longer routes through $E_q$, $I_a$ and $I_h$.
Local stability follows from the next-generation theorem. Because $\mathcal R_c$ is linear in
$1 - \epsilon_M c_M$, efficacy and coverage are interchangeable: only their product matters, and
low-efficacy masks need correspondingly higher coverage.

## Sources

- C. N. Ngonghala, E. Iboi, S. Eikenberry, M. Scotch, C. R. MacIntyre, M. H. Bonds, A. B. Gumel,
  "Mathematical assessment of the impact of non-pharmaceutical interventions on curtailing the 2019
  novel Coronavirus", Mathematical Biosciences 325 (2020) 108364, Section 3.1, Eq. (3.1) and
  Theorem 3.1, <https://doi.org/10.1016/j.mbs.2020.108364> (PMC7252217). The mask-threshold
  corollary is derived here from the structure of $F$ and $V$.
