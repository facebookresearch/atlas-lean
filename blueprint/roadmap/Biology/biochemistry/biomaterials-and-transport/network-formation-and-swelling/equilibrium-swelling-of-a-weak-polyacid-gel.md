# Equilibrium swelling of a weak-polyacid gel

In the electroneutral model of Marcombe et al., a gel carrying weak acid groups swells by a Flory–Rehner balance plus an ionic osmotic pressure from unbalanced mobile ions, whose size depends on how many groups are ionized at the bath's pH and salt concentration.

Model ingredients. (1) Dissociation AH ⇌ A⁻ + H⁺ inside the gel, at equilibrium,

$$\frac{[A^-][H^+]_{in}}{[AH]} = K_a ,$$

so the ionized fraction of acid groups is $K_a/(K_a + [H^+]_{in})$, where $[H^+]_{in}$ is the proton concentration in the gel. (2) Conservation of acid groups, $C_{AH} + C_{A} = f/v$ in nominal concentrations per unit reference volume, with $f/v$ the density of acid groups defined in the source. (3) Electroneutrality of the gel (fixed charges plus mobile ions) and of the external solution, with mobile monovalent ions distributed by Donnan equations $c_+/\bar c_+ = c_{H^+}/\bar c_{H^+}$ and $c_-/\bar c_- = \bar c_{H^+}/c_{H^+}$ (inside versus bath), a ratio form that presumes positive concentrations of each species; limits in which a species vanishes are taken from the original balances. (4) The network free energy $W_{net} = \tfrac12 NkT[F_{iK}F_{iK} - 3 - 2\log\det F]$, plus Flory–Huggins mixing, ideal mobile-ion and dissociation terms. Equilibrium is a variational statement over displacement and concentrations.

Limits stated by the source. When $pH \ll pK_a$ all groups are associated, $C_{AH} = f/v$, the network is neutral and the ionic osmotic pressure vanishes; when $pH \gg pK_a$ all groups are dissociated, $C_A = f/v$, counterions concentrate in the gel and the ionic osmotic pressure is positive, so the network imbibes more solvent than in the associated limit.

## Context

Research level (continuum mechanics of gels). In the source's numerical free-swelling results (Fig. 4, $pK_a = 4.3$), at fixed counterion concentration the swelling ratio moves between these two limits as pH varies, and at fixed pH it depends non-monotonically on counterion concentration (at pH 5 it first rises by ion exchange and then drops as the gel behaves like a neutral gel at high salt). These are computed trends for the specified baths and free swelling, not general monotonicity theorems; constrained swelling (the source's other cases) behaves differently.

## Depends on

- [Free-swelling equilibrium of a neutral gel (Flory–Rehner)](free-swelling-equilibrium-of-a-neutral-gel.md)
- [Existence of a positive root of the monoprotic acid equation](../../../../Chemistry/solutions-and-aqueous-equilibria/dissociation-of-a-monoprotic-acid/monoprotic-acid-h-exists.md)

## Proof depends on

None.

## Expansion

Before a theorem: write the full free energy (mobile-ion and dissociation terms with reference activities), carry out the source's Legendre transformation, and derive the free-swelling equations as functions of bath pH and counterion concentration; then prove the two limits as lemmas from the original balances (the low-pH limit should reduce to the neutral equation). Any monotonicity statement must specify the bath variables held fixed and the loading.

## Sources

- R. Marcombe, S. Cai, W. Hong, X. Zhao, Y. Lapusta and Z. Suo, "A theory of constrained swelling of a pH-sensitive hydrogel", Soft Matter 6, 784–793 (2010), <https://doi.org/10.1039/b917211d>; author-hosted copy read at <http://zhao.mit.edu/wp-content/uploads/2019/01/25.pdf>: Section 1 (electroneutrality and its Debye-length limitation); Section 2, Eqs. (2.2) and (2.13); Section 3, Eq. (3.5) and the Donnan relations (3.13)–(3.14); Section 4, Eqs. (4.1)–(4.3) and Fig. 4 (free swelling versus pH and counterion concentration, $pK_a = 4.3$)
