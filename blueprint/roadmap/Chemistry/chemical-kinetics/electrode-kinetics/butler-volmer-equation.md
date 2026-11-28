# Butler–Volmer equation

The Butler–Volmer equation models the net Faradaic current density of an electrode reaction at fixed surface composition as $j(\eta)=j_0\big(e^{\alpha_anf\eta}-e^{-\alpha_cnf\eta}\big)$, $f=F/RT$, a difference of anodic and cathodic exponential branches with exchange current density $j_0$.

For an electrode reaction $\mathrm O+n\,e^-\rightleftharpoons\mathrm R$ ($n\ge1$ electrons) at temperature $T>0$,
let $E_{\mathrm{eq}}$ be the equilibrium potential of the electrode at the given surface composition (its
zero-net-current potential, a model input), $\eta=E-E_{\mathrm{eq}}$ the (activation) overpotential and $f=F/(RT)$.
The **Butler–Volmer equation** is the constitutive model

$$j(\eta)=j_0\Big(e^{\alpha_anf\eta}-e^{-\alpha_cnf\eta}\Big)$$

for the net Faradaic current density, counted positive for net oxidation (anodic) in the IUPAC convention.
The parameters, held fixed along the sweep in $\eta$, are the exchange current density $j_0>0$ (the common
magnitude of the anodic and cathodic partial current densities at $\eta=0$, which depends on the surface
composition) and the anodic and cathodic transfer coefficients $\alpha_a,\alpha_c>0$. As a phenomenological law the two
coefficients are independent. For a single-step one-electron reaction obeying detailed balance they are
complementary, $\alpha_c=\alpha$ and $\alpha_a=1-\alpha$ with a symmetry factor $0<\alpha<1$. The ratio of the anodic (oxidation)
partial current density to the magnitude of the cathodic (reduction) partial current density is
$j_a/|j_c|=e^{(\alpha_a+\alpha_c)nf\eta}$, with $j_a=j_0e^{\alpha_anf\eta}$ and $j_c=-j_0e^{-\alpha_cnf\eta}$. This positive ratio equals $e^{nf\eta}$ for every $\eta$
exactly when $\alpha_a+\alpha_c=1$, an algebraic condition of which the complementary single-step coefficients are the standard example. The equation describes activation-controlled kinetics; it neglects mass transport
and diffuse-charge effects.

## Context

Undergraduate electrochemistry and the standard kinetic input of battery and fuel-cell models. Microscopic electron-transfer theories (Marcus, Marcus–Hush–Chidsey) give other current–overpotential laws that are compared with it on Tafel plots.

## Depends on

None.

## Proof depends on

None.

## Expansion

A model definition. Bazant's Eq. (27) writes the same law for the net reduction current, $I=I_0(e^{-\alpha_cne\eta/k_BT}-e^{\alpha_ane\eta/k_BT})$; per mole $e/k_B=F/R$, and $j=-I/A$ for electrode area $A$.

## Sources

- M. Z. Bazant, Theory of chemical kinetics and charge transfer based on nonequilibrium thermodynamics, *Accounts of Chemical Research* 46 (2013), 1144–1160; numbers from arXiv:1208.1587v5, section “Generalized Butler–Volmer kinetics”, Eq. (27) and the single-step relations $\alpha_a=1-\alpha$, $\alpha_c=\alpha$. [arXiv:1208.1587v5](https://arxiv.org/abs/1208.1587v5); [doi:10.1021/ar300145c](https://doi.org/10.1021/ar300145c)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 72 (overpotential $\eta=E-E_{\mathrm{eq}}$, exchange current density, transfer coefficients with $\alpha_a=1-\alpha_c$ at the same potential, and Tafel slope, notes 23–26). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
