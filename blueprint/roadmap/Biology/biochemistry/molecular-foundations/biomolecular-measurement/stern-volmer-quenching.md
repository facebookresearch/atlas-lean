# Stern–Volmer fluorescence quenching

For collisional (dynamic) quenching, the ratio of fluorescence intensities without and with quencher is linear in the free quencher concentration, $F_0/F=\tau_0/\tau=1+k_q\tau_0[Q]$; adding static quenching by ground-state dark complexes multiplies this by a second linear factor, and within that product model the Stern–Volmer plot curves upward exactly when both constants are positive.

**Setting.** A fluorophore with a single emitting class is excited at constant intensity, with excitation and detection unchanged by the quencher and the intensity corrected for inner-filter absorption (or the sample optically dilute). In the absence of quencher its excited state decays with total rate $k_f+k_{nr}$ (radiative $k_f>0$ plus nonradiative), so its lifetime is $\tau_0=1/(k_f+k_{nr})$ and its quantum yield $\phi_0=k_f\tau_0$. A quencher at free concentration $[Q]\ge0$ deactivates excited fluorophores by encounters with bimolecular rate constant $k_q\ge0$ (dynamic quenching), without changing the intrinsic rates, and may also bind the ground-state fluorophore into a non-fluorescent complex with association constant $K_S\ge0$ (static quenching). Fluorescence intensity is proportional to the fluorescent fraction times its quantum yield.

**Statement.**

1. *Dynamic quenching only.* The quantum yield becomes $k_f/(k_f+k_{nr}+k_q[Q])$, the lifetime $\tau=1/(k_f+k_{nr}+k_q[Q])$, and

$$\frac{F_0}{F}=\frac{\tau_0}{\tau}=1+k_q\tau_0[Q]=1+K_{SV}[Q],\qquad K_{SV}=k_q\tau_0.$$

2. *Static and dynamic quenching.* If a fraction $K_S[Q]/(1+K_S[Q])$ of fluorophores is held in non-fluorescent complexes at equilibrium and the free fluorophores are quenched dynamically,

$$\frac{F_0}{F}=\big(1+k_q\tau_0[Q]\big)\big(1+K_S[Q]\big),$$

while the lifetime ratio of the emitting population still equals $1+k_q\tau_0[Q]$. Within this two-factor model the plot of $F_0/F$ against $[Q]$ curves upward exactly when both $k_q\tau_0>0$ and $K_S>0$. Upward curvature in data does not by itself identify both mechanisms: other models also produce it, for example a "sphere of action" in which a fluorophore with a quencher within a fixed volume is dark, giving an exponential factor (discussed by Lakowicz and Weber), or uncorrected absorption artefacts.

3. *Diffusion-controlled limit.* If every encounter quenches and encounters are governed by ordinary three-dimensional radial diffusion to an absorbing contact sphere, $k_q=4\pi aDN'$ with $D$ the sum of the diffusion coefficients and $a$ the sum of the molecular radii. With $a$ in cm, $D$ in cm$^2$ s$^{-1}$ and $N'=N_A/1000$ (molecules per millimole, as in the source, since 1 M is 1 mmol cm$^{-3}$), $k_q$ is in M$^{-1}$s$^{-1}$ and $K_{SV}$, $K_S$ are in M$^{-1}$; in SI units with $a$ in m, $D$ in m$^2$ s$^{-1}$ and $N_A$, $k_q$ is in m$^3$mol$^{-1}$s$^{-1}$ with $[Q]$ in mol m$^{-3}$. This is the rate constant $4\pi DR$ of the [Smoluchowski steady radial current](../../../not-yet-classified/diffusion-limited-rate/current-eq-smoluchowski.md) with $R=a$, expressed in molar units.

## Context

Undergraduate to graduate biophysical chemistry. Quenching by oxygen, iodide or acrylamide probes the solvent accessibility and structural fluctuations of fluorophores in proteins; Lakowicz and Weber found near-diffusion-limited oxygen quenching of free fluorophores, including tryptophan, in the systems studied, and used the method to detect access-dependent protection of macromolecule-bound probes (empirical results). The Artzi RNA-triple-helix design places fluorophores and a dark quencher on separate strands and reads near-complete quenching at a 1:1:1 molar ratio as evidence that the strands are assembled in close proximity (Conde et al. 2016, Fig. 2a); that is quenching within a complex, not the diffusional law in item 1, which it does not test.

## Depends on

- [Smoluchowski's steady radial current](../../../not-yet-classified/diffusion-limited-rate/current-eq-smoluchowski.md)

## Proof depends on

None.

## Expansion

Proof: item 1 is the ratio of the steady-state quantum yields, $(k_f+k_{nr}+k_q[Q])/(k_f+k_{nr})$, and of the lifetimes. Item 2: the free (emitting) fraction is $1/(1+K_S[Q])$ and each free fluorophore is quenched as in item 1; complexes contribute no emission and do not change the free population's lifetime. Expanding, $F_0/F=1+(k_q\tau_0+K_S)[Q]+k_q\tau_0K_S[Q]^2$, whose second derivative in $[Q]$ is $2k_q\tau_0K_S$. Item 3 identifies $k_q$ with $4\pi DR$ from the Smoluchowski page and converts per-molecule to molar units. The LibreTexts course page writes an intermediate step of the Stern–Volmer derivation without the factor $\tau_0$; the dimensionally correct constant is $K_{SV}=k_q\tau_0$, as in Lakowicz and Weber.

Remaining decomposition before the page can be marked ready: (i) a definition page for the photophysical kinetic model (constant excitation, single emitting class, intrinsic rates unchanged); (ii) the static-complex equilibrium as a binding lemma (it is the [single-class isotherm](../ligand-binding-equilibria/single-class-binding-isotherm.md) for fluorophore–quencher binding, applied with free $[Q]$); (iii) the unit conversion in item 3 as an explicit lemma.

## Sources

- J. R. Lakowicz and G. Weber, "Quenching of fluorescence by oxygen. A probe for structural fluctuations in macromolecules", *Biochemistry* 12(21) (1973), 4161–4170, [doi.org](https://doi.org/10.1021/bi00745a020); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6959846/), Introduction/Theory (the Stern–Volmer equation $F_0/F=1+k\tau_0[O_2]$, $K=k\tau_0$, the diffusion-controlled $k=4\pi aDN'$ with $N'$ molecules per millimole and the worked value in cm units, and the combined static–dynamic form) and the later discussion of the sphere-of-action model with its exponential factor.
- Providence College CHM 331 *Advanced Analytical Chemistry 1*, LibreTexts, Section 10.3.4 "The Fluorescence Lifetime and Quenching" (read at [chem.libretexts.org](http://chem.libretexts.org/Courses/Providence_College/CHM_331_Advanced_Analytical_Chemistry_1/10:_Molecular_Luminescence_Spectrometry/10.03:_Applications_of_Photoluminescence_Methods/10.3.04:_The_Fluorescence_Lifetime_and_Quenching)): quantum yields with and without quencher, the Stern–Volmer equation and $F_0/F=\tau_0/\tau$ for collisional quenching only.
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/), Results and Fig. 2a (context only).
