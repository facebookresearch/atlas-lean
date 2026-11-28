# Equilibrium swelling of a weak-polyacid gel

In the model of Marcombe et al., an electroneutral gel bearing weak acid groups swells under a balance of network stretching, polymer–solvent mixing and an ionic osmotic pressure from unbalanced mobile ions; how many groups dissociate depends on the external solution's pH and counterion concentration.

Model ingredients. The reference state is the dry, stress-free network. Nominal concentrations $C_a$ are numbers of particles per unit reference volume; true concentrations $c_a = C_a/\det F$ are numbers per unit current volume of the gel; barred $\bar c_a$ are numbers per unit volume of the external solution; square brackets denote molar concentrations in the gel.

1. Dissociation. The reaction AH ⇌ A⁻ + H⁺ is at equilibrium in the gel, $[A^-][H^+]/[AH] = K_a$, with $K_a$ having units of concentration. Rearranged, the dissociated fraction of acid groups is $K_a/(K_a + [H^+])$, where $[H^+]$ is the hydrogen-ion concentration inside the gel; the bath pH fixes $\bar c_{H^+}$, and in a charged network the in-gel number density $c_{H^+}$ and the bath number density $\bar c_{H^+}$ need not agree.
2. Conservation of acid groups: $C_{AH} + C_A = f/v$, where $f$ is the number of acid groups divided by the number of monomers and $v$ is the volume per monomer.
3. Electroneutrality in the gel, $C_{H^+} + C_+ = C_A + C_-$, and in the external solution, with water dissociation neglected and counterions and co-ions monovalent.
4. Molecular incompressibility $1 + v_SC_S = \det F$, with $C_S$ the nominal solvent concentration and $v_S$ the volume per solvent molecule; the ions are dilute and their volume is neglected.
5. Nominal free energy density (per unit dry volume) $W = W_{net} + W_{sol} + W_{ion} + W_{dis}$, with network stretching $W_{net} = \tfrac12 NkT[F_{iK}F_{iK} - 3 - 2\log\det F]$ ($N$ chains per unit dry volume), Flory–Huggins mixing with parameter $\chi$, the entropy of mixing of the dilute ions, and the entropy and enthalpy of dissociation.

Equilibrium is a variational statement over the displacement and the concentrations. For mobile ions it gives the Donnan equations $c_+/\bar c_+ = c_{H^+}/\bar c_{H^+}$ and $c_-/\bar c_- = \bar c_{H^+}/c_{H^+}$ (a ratio form that presumes positive concentrations of each species). The true (Cauchy) stress is

$$\sigma_{ij} = \frac{NkT}{\det F}\left(F_{iK}F_{jK} - \delta_{ij}\right) - \left(P_{sol} + P_{ion}\right)\delta_{ij}, \qquad P_{ion} = kT\left(c_{H^+} + c_+ + c_- - \bar c_{H^+} - \bar c_+ - \bar c_-\right),$$

where $P_{sol}$ is the osmotic pressure of polymer–solvent mixing and $P_{ion}$ that of the imbalance of mobile ions between gel and solution.

Limiting regimes stated by the source. In the fully associated limit, which the source associates with $pH \ll pK_a$, $C_{AH} = f/v$ and $C_A = 0$; the network is neutral, each ion species is equally distributed between gel and solution, and $P_{ion} = 0$. In the fully dissociated limit ($pH \gg pK_a$), $C_{AH} = 0$ and $C_A = f/v$; counterions neutralize the fixed charges, mobile ions are more concentrated in the gel than in the solution, $P_{ion} > 0$, and the network imbibes more solvent than in the associated limit. These are idealized limits: for $K_a > 0$ and $0 < [H^+] < \infty$ the dissociated fraction lies strictly between 0 and 1, and the source's pH 2 and pH 9 examples approach the two limits.

## Context

Research level (continuum mechanics of gels). The electroneutral description ignores the electric double layer at the gel surface and so misses phenomena on the scale of the Debye length. In the source's free-swelling calculations ($Nv = 10^{-3}$, $\chi = 0.1$, $f = 0.05$, $v = v_S$, $pK_a = 4.3$, a value the authors call commonly accepted for carboxylic acids):

- The gel swells more when the solution has low concentrations of both hydrogen ions and counterions, and less when it is concentrated in either.
- At fixed counterion concentration, the swelling ratio as a function of pH is read through the two limits.
- At pH 5, the swelling ratio first increases with counterion concentration (ion exchange) and then drops at very high counterion concentration, where the gel behaves like a neutral gel.

These are computed trends for the stated parameters, not general theorems; the source treats constrained swelling separately.

## Depends on

- [Free-swelling equilibrium of a neutral gel (Flory–Rehner)](free-swelling-equilibrium-of-a-neutral-gel.md)
- [Existence of a positive root of the monoprotic acid equation](../../../../Chemistry/solutions-and-aqueous-equilibria/dissociation-of-a-monoprotic-acid/monoprotic-acid-h-exists.md)

## Proof depends on

None.

## Expansion

Before a theorem: write the full free energy (mobile-ion and dissociation terms with reference activities), carry out the source's Legendre transformation, and derive the free-swelling equations as functions of bath pH and counterion concentration; then prove the two limits as lemmas from the original balances (the low-pH limit should reduce to the neutral equation). Any monotonicity statement must specify the bath variables held fixed and the loading.

## Sources

- R. Marcombe, S. Cai, W. Hong, X. Zhao, Y. Lapusta and Z. Suo, "A theory of constrained swelling of a pH-sensitive hydrogel", Soft Matter 6, 784–793 (2010), <https://doi.org/10.1039/b917211d>; author-hosted copy read at <http://zhao.mit.edu/wp-content/uploads/2019/01/25.pdf>: Section 1 (electroneutrality and the Debye-length limitation); Section 2, Eqs. (2.1)–(2.2) (dissociation), the paragraph on the four species of the external solution (water dissociation neglected, monovalent ions), Eq. (2.13) (acid groups), Eqs. (2.14)–(2.15) (electroneutrality), Eq. (2.16) (incompressibility) and the variational statement (2.8); Section 3, Eqs. (3.4)–(3.8) (free energy), the definition of true concentrations $C_a = c_a\det F$, Eqs. (3.10)–(3.12) (stress and osmotic pressures) and (3.13)–(3.14) (Donnan equations), and the parameter paragraph ($Nv$, $\chi$, $f$, $pK_a = 4.3$), journal p. 788; Section 4, Eqs. (4.1)–(4.3) (limiting regimes) and the free-swelling discussion of Fig. 4, including the pH 2 and pH 9 cases, journal pp. 788–789
