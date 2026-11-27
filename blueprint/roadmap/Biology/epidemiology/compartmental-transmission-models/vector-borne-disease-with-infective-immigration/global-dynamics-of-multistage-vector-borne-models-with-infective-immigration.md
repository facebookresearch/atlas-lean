# Global dynamics of multistage vector-borne models with infective immigration

**Model.** Hosts are susceptible $S_h$, latent $E_h$, infectious in stages $\mathbf{I}_h = (I_1, \dots, I_n)^{\mathsf T}$, or recovered; vectors are susceptible $S_v$, latent $E_v$ or infectious $I_v$, with constant total vector population $N_v = \pi_v/(\mu_v + \delta_v)$ and asymptotically constant host population $N_h$. Host recruitment $\pi_h$ arrives latent with probability $p$, infectious in stage $i$ with probability $p_i$ (vector $\mathbf{p}$) and recovered with probability $p_{n+1}$. With biting rate $a$, vector-to-host transmission $\beta_{vh}$, stage-specific host-to-vector transmission vector $\boldsymbol\beta = (\beta_1, \dots, \beta_n)^{\mathsf T}$, stage-exit rates $\alpha = (\alpha_1, \dots, \alpha_n)$ and $M = G^{\mathsf T} + D^{\mathsf T}$ built from a strictly upper-triangular progression matrix $G$ and a strictly lower-triangular amelioration matrix $D$ (both nonnegative):

$$\dot S_h = \pi_h(1 - p - \mathbf{1}^{\mathsf T}\mathbf{p} - p_{n+1}) - a\beta_{vh} S_h \frac{I_v}{N_h} - \mu_h S_h, \qquad \dot E_h = p\pi_h + a\beta_{vh} S_h \frac{I_v}{N_h} - (\mu_h + \nu_h + \eta) E_h,$$

$$\dot{\mathbf{I}}_h = \pi_h \mathbf{p} + \nu_h E_h e_1 - (\operatorname{diag}(\alpha) - M)\mathbf{I}_h,$$

$$\dot S_v = \pi_v - a\frac{S_v}{N_h}\langle\boldsymbol\beta, \mathbf{I}_h\rangle - (\mu_v + \delta_v) S_v, \qquad \dot E_v = a\frac{S_v}{N_h}\langle\boldsymbol\beta, \mathbf{I}_h\rangle - (\mu_v + \nu_v + \delta_v) E_v, \qquad \dot I_v = \nu_v E_v - (\mu_v + \delta_v) I_v.$$

The natural simplex $\{S_h + E_h + \mathbf{1}^{\mathsf T}\mathbf{I}_h \le N_h,\ S_v + E_v + I_v \le N_v\}$ is compact and positively invariant. An equilibrium is **weakly endemic** if infection persists only in hosts ($E_v = I_v = 0$) and **strongly endemic** if vectors are infected too.

**Theorem.**

1. *(Equilibria.)* If $\boldsymbol\beta = 0$ there is a unique weakly endemic equilibrium. If $p \ne 0$ and $\langle\boldsymbol\beta, (\operatorname{diag}(\alpha) - M)^{-1} e_1\rangle \ne 0$, or if $\langle\boldsymbol\beta, (\operatorname{diag}(\alpha) - M)^{-1}\mathbf{p}\rangle \ne 0$, there is a unique strongly endemic equilibrium. Otherwise the threshold

$$\mathcal{N}_0^2 = \frac{a^2 \beta_{vh}\nu_v\nu_h}{\alpha_v(\mu_v + \delta_v)\,\alpha_h\,\mu_h}\,\frac{N_v}{N_h}\,\frac{\pi_h(1 - p - \mathbf{1}^{\mathsf T}\mathbf{p} - p_{n+1})}{N_h}\,\big\langle\boldsymbol\beta, (\operatorname{diag}(\alpha) - M)^{-1} e_1\big\rangle,$$

with $\alpha_h = \mu_h + \nu_h + \eta$ and $\alpha_v = \mu_v + \nu_v + \delta_v$, decides: a unique weakly endemic equilibrium if $\mathcal{N}_0^2 \le 1$, a unique strongly endemic one if $\mathcal{N}_0^2 > 1$. (The source's Theorem 3.1 states the first case as $\boldsymbol\beta \ne 0$ and $p \ne 0$; that fails when no transmitting stage is reachable from stage 1, e.g. $n = 2$, $G = D = 0$, $\boldsymbol\beta = (0,\beta_2)$, $p > 0$, $\mathbf{p} = \mathbf{0}$, where $I_2 \to 0$.)
2. *(Global stability.)* Every strongly endemic equilibrium is globally asymptotically stable whenever it exists, and so is every weakly endemic equilibrium.
3. *(No immigration of infected hosts: sharp threshold.)* If $p = 0$, $\mathbf{p} = \mathbf{0}$ and $p_{n+1} = 0$, then $\mathcal{R}_0^2 = \mathcal{N}_0^2(0, \mathbf{0}, 0)$ and: for $\mathcal{R}_0^2 \le 1$ the disease-free equilibrium is globally asymptotically stable; for $\mathcal{R}_0^2 > 1$ it is unstable and a unique endemic equilibrium exists and is globally asymptotically stable.

Consequently, once infectious hosts enter at a stage that transmits to vectors (directly or after progression or amelioration), the host–vector chain cannot be broken by reducing $\mathcal{R}_0$ alone.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

$M$ is Metzler and $\operatorname{diag}(\alpha) - M$ is a nonsingular M-matrix, so $(\operatorname{diag}(\alpha) - M)^{-1} \ge 0$: the vector $(\operatorname{diag}(\alpha) - M)^{-1} e_1$ collects the expected residence times in each infectious stage of a host entering stage 1, and pairing with $\boldsymbol\beta$ gives its total infectiousness to vectors. This is the host-to-vector factor of the next-generation matrix; $\mathcal{N}_0^2$ is the product of the two transmission legs (hence the square). Imported latent hosts, or imported infectious hosts whose stages lead to $\boldsymbol\beta$-weighted transmission, act as a source term, so no infection-free equilibrium exists. Global stability is proved with Volterra-type Lyapunov functions built from terms $x/x^* - 1 - \ln(x/x^*)$, combined with LaSalle's invariance principle; the asymptotically autonomous reduction of the host total justifies analyzing the compact system.

## Sources

- Derdei Mahamat Bichara, "Effects of migration on vector-borne diseases with forward and backward stage progression", Discrete and Continuous Dynamical Systems - B 24 (2019), 6297–6323, <https://doi.org/10.3934/dcdsb.2019140>. Published version of arXiv:1810.06777, cited next; locators there refer to the arXiv version.
- Derdei Bichara, "Effects of migration on vector-borne diseases with forward and backward stage progression", arXiv (2018). Section 2 (compact model), Lemma 2.1, Theorems 3.1–3.4. <https://doi.org/10.48550/arXiv.1810.06777>
