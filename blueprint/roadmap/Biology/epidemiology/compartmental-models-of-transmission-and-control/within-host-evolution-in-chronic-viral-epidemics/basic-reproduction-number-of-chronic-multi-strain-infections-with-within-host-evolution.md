# Basic reproduction number of chronic multi-strain infections with within-host evolution and treatment

**Baseline model.** A chronic viral infection (for example HIV) circulates as $n$ strains with the same phenotype. A person infected with strain $j$ is first acute ($I_{Aj}$), carrying only strain $j$. They then become chronic ($I_{Cj}$), and within-host evolution makes their viral population contain strain $i$ in average fraction $\alpha_{ij}$, where $\sum_i\alpha_{ij} = 1$ and $\alpha_{ii} \ne 0$. Chronic cases enter fully suppressive treatment ($T$) at rate $u_T$. With population turnover $\mu$, progression rate $\gamma$ and population fractions,

$$
\begin{aligned}
\dot I_{Ai} &= \phi_i(X)S - (\gamma + \mu)I_{Ai}, & \dot I_{Ci} &= \gamma I_{Ai} - (u_T + \mu)I_{Ci},\\
\dot T &= u_T\textstyle\sum_i I_{Ci} - \mu T, & \dot S &= \mu - \textstyle\sum_i\phi_i(X)S - \mu S,
\end{aligned}
\qquad \phi_i(X) = \beta_C\Big(\xi I_{Ai} + \sum_j\alpha_{ij}I_{Cj}\Big),
$$

where $\xi$ is the relative infectiousness of the acute stage.

**Theorem (baseline).** For every within-host mixing matrix $(\alpha_{ij})$ as above, the controlled basic reproduction number is

$$ R_0^\alpha(u_T) = \beta_C\,\frac{\xi(u_T + \mu) + \gamma}{(\gamma + \mu)(u_T + \mu)} = \frac{\xi\beta_C}{\gamma + \mu} + \frac{\beta_C\gamma}{(\gamma + \mu)(u_T + \mu)} , $$

which does not depend on $\alpha$. Within-host emergence of strains without phenotypic novelty leaves the epidemic threshold unchanged. If $R_0^\alpha(0) > 1$, treatment is *efficient* (some finite $u_T^* \ge 0$ gives $R_0^\alpha(u_T^*) = 1$) if and only if $\xi\beta_C < \gamma + \mu$: acute-stage transmission alone must be subcritical, because treatment reaches only chronic cases.

**Theorem (phenotypic variation, imperfect treatment, prophylaxis).** Let strains differ in transmissibility $\beta_{Ci}$ and in treatment failure rate $\zeta_i$ (treated people $T_i$ return to $I_{Ci}$). Let susceptibles enter prophylaxis $P$ at rate $u_P$, leaving it at rate $\delta$, with strain-specific protection $\psi_i$. Then

$$ R_0^\beta(u_T,u_P) = \frac{\bar\beta_C(\gamma + \xi\mu)}{(\gamma + \mu)\mu}\,\rho\big(Q(u_P)N(u_T)\big), $$

where $\bar\beta_C = \max_i\beta_{Ci}$ and $\rho$ is the spectral radius. Here $Q(u_P) = \bar\beta_C^{-1}B_C\big[E_n - P_{DFE}(u_P)\Psi\big]$, with $B_C = \operatorname{diag}(\beta_{Ci})$, $\Psi = \operatorname{diag}(\psi_i)$ and $P_{DFE}(u_P) = u_P/(\delta + \mu + u_P)$ the prophylaxis coverage at the disease-free equilibrium. Further, $N(u_T) = \frac{1}{\gamma + \xi\mu}\big[\xi\mu E_n + \gamma A\,\Delta(u_T)\big]$ with $A = (\alpha_{ij})$ and $\Delta(u_T) = (Z + (\mu + u_T)E_n)^{-1}(Z + \mu E_n)$, $Z = \operatorname{diag}(\zeta_i)$. Now within-host evolution does matter: it enters through $A\Delta(u_T)$, coupling transmissibility, resistance to therapy and prophylaxis efficacy across strains.

## Expansion

Both results come from the next-generation matrix at the disease-free equilibrium. In the baseline model, summing the infection equations over strains gives a closed two-stage system, because $\sum_i\alpha_{ij} = 1$: whatever strain a chronic case transmits, it produces one acute infection per contact. The spectral radius is therefore the mean number of infections over the acute period ($\xi\beta_C/(\gamma+\mu)$) plus that over the chronic period. For the extended model this symmetry breaks. The next-generation matrix factors into the transmissibility and prophylaxis part $Q$ and the progression, treatment and within-host-mixing part $N$, and $R_0$ is the Perron root of their product. The column stochasticity of $A$ and of its convex combinations controls the dominant eigenvectors.

## Sources

- Dmitry Gromov and Ethan O. Romero-Severson, "Within-host phenotypic evolution and the population-level control of chronic viral infections by treatment and prophylaxis", arXiv:1910.03975 (2019), Section 2 (models), Section 3 (Theorem 3.1, Definition 3.1, Lemma 3.2, Theorem 3.3), Section 4 (endemic equilibria), <https://doi.org/10.48550/arXiv.1910.03975>.
