# Chemical potential in terms of relative activity

The relative activity of a species is the positive number $a_i$ for which its chemical potential is $\mu_i=\mu_i^\circ+RT\ln a_i+z_iF\phi$, measured from a chosen standard state and the electric potential $\phi$ of its phase.

Let $T>0$ be the temperature, $R>0$ the gas constant and $F>0$ the Faraday constant. Let species $i$ have
charge number $z_i\in\mathbb{Z}$ and lie in a phase of electric (inner) potential $\phi$, and let $\mu_i$ be its
chemical potential, taken as given: the partial molar Gibbs energy $\mu_i=(\partial G/\partial n_i)_{T,p,n_{j\ne i}}$
of the phase (for an ion it is also called the electrochemical potential). Fix a standard state for $i$
(pure substance, or a solute standard state on a mole-fraction, concentration or molality basis at the
standard pressure $p^\circ$); its standard chemical potential $\mu_i^\circ$ depends only on $T$ and that choice.
The **relative activity** of $i$ is

$$a_i=\exp\!\Big(\frac{\mu_i-\mu_i^\circ-z_iF\phi}{RT}\Big)>0,\qquad\text{equivalently}\qquad \mu_i=\mu_i^\circ+RT\ln a_i+z_iF\phi .$$

It is dimensionless; $a_i=1$ for the species in its standard state in a phase at $\phi=0$, and for an
uncharged species ($z_i=0$) the potential term vanishes. For a solute on the molality basis at
$p=p^\circ$ one writes $a_i=\gamma_{i}\,m_i/m^\circ$ for molality $m_i>0$, with $m^\circ=1\ \mathrm{mol\,kg^{-1}}$,
which defines the activity coefficient $\gamma_i>0$; ideal-dilute behaviour is $\gamma_i\to1$ as all solute
molalities tend to zero. Away from $p^\circ$ a pressure factor multiplies $a_i$; it is usually close to one,
and replacing it by one is an approximation that is stated wherever it is used.

## Context

Undergraduate physical chemistry. The activity form of the chemical potential is the common input of the reaction quotient, the Nernst equation and the Debye–Hückel activity coefficients. For an ideal-dilute ion on the concentration basis, $a_i=c_i/c^\circ$ with positive concentration $c_i$ and standard concentration $c^\circ$; the [molar electrochemical potential](../../../Biology/mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/electrochemical-potential.md) used for membrane potentials is this case written with a dimensionless concentration, the term $-RT\ln c^\circ$ being absorbed into its standard value.

## Depends on

None.

## Proof depends on

None.

## Expansion

A definition: given $\mu_i$, $\mu_i^\circ$ and $\phi$, the exponential formula gives a unique positive $a_i$, and taking logarithms gives the additive form. The molality-basis activity coefficient is the ratio $\gamma_i=a_im^\circ/m_i$.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.8.1, Eq. 11.8.1 (citing Eq. 10.1.9) and Sec. 14.4 for $a_+=\gamma_+m_+/m^\circ$ with pressure factors set to unity. [Section 11.8.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.08%3A_The_Thermodynamic_Equilibrium_Constant)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 71 (electrochemical potential $\tilde\mu_B=\mu_B^\circ+RT\ln a_B+z_BF\phi$, note 11). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
