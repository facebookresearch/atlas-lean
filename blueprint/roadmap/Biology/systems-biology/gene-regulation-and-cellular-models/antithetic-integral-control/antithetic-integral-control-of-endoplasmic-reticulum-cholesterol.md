# Antithetic integral control of endoplasmic-reticulum cholesterol

**Setting.** A mass-action model of cellular cholesterol regulation has 13 dynamic species and the
input $C_L$ (free LDL cholesterol taken up through the LDL receptor $R$). The controller core is a
sequestration (annihilation) pair: the SREBP/Scap/Insig complex $S_{ci}$, produced constitutively at
rate $\mu$, and cholesterol $C$ released into the ER lumen from ER cholesterol $C_e$ at rate
$\theta C_e$, which form a complex retained in the ER ($S_{ci} + C \to \varnothing$, rate constant
$\eta$):

$$\frac{dS_{ci}}{dt} = \mu - \eta S_{ci} C, \qquad \frac{dC}{dt} = \theta C_e - \eta S_{ci} C.$$

The remaining equations include, with positive rate constants,

$$\frac{dC_f}{dt} = k_3 C_L R - k_4 C_f, \qquad \frac{dC_p}{dt} = k_4 C_f - k_5 C_p + k_6 C_e, \qquad \frac{dE}{dt} = k_7 C_e - k_8 E,$$

$$\frac{dC_e}{dt} = k_5 C_p - k_6 C_e + k_9 H_R H - k_{12} C_e - k_7 C_e + k_8 E, \qquad \frac{dH}{dt} = \alpha - k_9 H_R H,$$

where $R$ (LDL receptor) and $H_R$ (HMGCR) are driven by $S_{ci}$ through further linear and bilinear
equations.

**Statement.** The difference of the two controller equations is independent of the sequestration
rate:

$$\frac{d}{dt}\big(C - S_{ci}\big) = \theta C_e - \mu,$$

so $C - S_{ci}$ is an integral of the regulation error of $C_e$ (antithetic integral control). The
two-variable elimination ideal of the 13 steady-state polynomials onto $(C_e, C_L)$ is

$$\langle f_1, \dots, f_{13}\rangle \cap \mathbb{R}[C_e, C_L] = \langle \theta C_e - \mu \rangle,$$

an RPA polynomial of order zero in the input. Hence at every positive steady state

$$C_e = \frac{\mu}{\theta}, \qquad E = \frac{k_7 \mu}{k_8 \theta}, \qquad C_p = \frac{(k_6 + k_{12})\mu - \theta\alpha}{k_5 \theta}, \qquad C_f = \frac{k_{12}\mu - \theta\alpha}{k_4 \theta},$$

independently of $C_L$ and of all other parameters: ER cholesterol and these three upstream species
exhibit robust perfect adaptation whenever the steady state is stable, while the other nine species
settle at levels that depend on $C_L$. The network has deficiency $6$ and splits into algebraically
independent subnetworks of deficiencies $1$ and $5$; the Shinar–Feinberg criterion applied to the
deficiency-one subnetwork (non-terminal complexes $C_e$ and $\varnothing$ differ in one species)
identifies $C_e$ as the RPA species.

## Depends on

- [Perfect adaptation](../../integral-feedback-and-perfect-adaptation/has-perfect-adaptation.md)

## Expansion

In the antithetic motif the two controller species are produced by the reference ($\mu$) and by the
regulated output ($\theta C_e$) and annihilate each other; subtracting their equations cancels the
nonlinear sequestration term exactly, leaving an integrator whose only steady state forces
$\theta C_e = \mu$, whatever the disturbance. The other set points follow by back-substitution in the
steady-state equations: $E$ from the $E$ equation, $k_9 H_R H = \alpha$ from the $H$ equation, then
$C_p$ from the $C_e$ equation and $C_f$ from the $C_p$ equation. The Gröbner-basis computation
certifies that this linear combination is the unique coordinate change producing an RPA polynomial,
and that the network has no linear conservation laws. Biologically, the sequestration is the
binding of cholesterol excluded from the ER membrane to the SREBP/Scap/Insig complex, which retains it
in the ER and blocks the release of SREBP transcription factors.

## Sources

- R. Scheepers, R. P. Araujo, "Robust homeostasis of cellular cholesterol is a consequence of endogenous antithetic integral control", Frontiers in Cell and Developmental Biology 11 (2023) 1244297, <https://doi.org/10.3389/fcell.2023.1244297> (PMC10570530). Section 3 (deficiency), Section 4.1 (independent subnetworks, Shinar–Feinberg), Section 4.2, Eqs. (1)–(16).
