# Debye–Hückel screened potential around an ion

In the linearized Poisson–Boltzmann model with positive ionic strength, the mean potential around a central ion of charge $z_ie$ and closest-approach distance $a$ is $\phi(r)=\frac{z_ie}{4\pi\varepsilon r}\frac{e^{\kappa(a-r)}}{1+\kappa a}$ for $r\ge a$.

Model (Debye–Hückel). A central ion of charge $z_ie$ ($z_i\ne0$) sits in a solvent of permittivity
$\varepsilon=\varepsilon_r\varepsilon_0>0$ at temperature $T>0$; other ions $j$, with bulk amount concentrations
$c_j\ge0$ in mol m$^{-3}$, charge numbers $z_j$ and $\sum_jc_jz_j=0$, cannot approach closer than $a>0$. Their local
concentrations follow the Boltzmann law $c_j'=c_je^{-z_je\phi/k_BT}$ linearized to $c_j'\approx c_j(1-z_je\phi/k_BT)$,
so for $r>a$ the charge density is $\rho=-\varepsilon\kappa^2\phi$ with

$$\kappa=\sqrt{\frac{2N_A^2e^2I_c}{\varepsilon_r\varepsilon_0RT}}>0,$$

where $I_c=\tfrac12\sum_jc_jz_j^2$ is the [ionic strength](ionic-strength.md) on the concentration basis (SI, mol m$^{-3}$)
and is assumed **positive**. Let $\phi\in C^2([a,\infty))$ satisfy

1. $\frac1{r^2}\frac{d}{dr}\big(r^2\phi'(r)\big)=\kappa^2\phi(r)$ for $r>a$ (Poisson's equation with the linearized charge density);
2. decay: $r\phi(r)$ is bounded on $[a,\infty)$;
3. the field at $r=a$ is that of the central charge alone, $-4\pi\varepsilon a^2\phi'(a)=z_ie$.

Then

$$\phi(r)=\frac{z_ie}{4\pi\varepsilon r}\,\frac{e^{\kappa(a-r)}}{1+\kappa a}\qquad(r\ge a),$$

the ion atmosphere is electroneutral with respect to the central ion, $\int_a^\infty\rho\,4\pi r^2\,dr=-z_ie$, and the
potential of the atmosphere alone, $\phi_{\mathrm{atm}}(r)=\phi(r)-z_ie/(4\pi\varepsilon r)$, is
$\phi_{\mathrm{atm}}(a)=-\frac{z_ie}{4\pi\varepsilon}\frac{\kappa}{1+\kappa a}$. The hypothesis $I_c>0$ is needed: with no other ions
($\kappa=0$) there is no atmosphere and the decaying solution is the bare Coulomb potential.

## Context

Graduate physical chemistry. $1/\kappa$ is the Debye screening length of the electrolyte; the same linearized equation governs the diffuse part of an electrode's double layer.

## Depends on

- [Ionic strength](ionic-strength.md)

## Proof depends on

- [A bounded steady state on the half-line decays as e^(−x/λ)](../../../Biology/mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/eq-exp-of-bounded.md)

## Expansion

Put $u(r)=r\phi(r)$; hypothesis 1 becomes $u''=\kappa^2u$ on $[a,\infty)$ and hypothesis 2 says $u$ is bounded. With $V(x)=u(a+x)$ and $I(x)=-u'(a+x)$, $(V,I)$ is a [steady state of the passive cable](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) with $r_i=1$, $r_m=\kappa^{-2}$ on $[0,\infty)$, so the half-line lemma gives $u(r)=u(a)e^{-\kappa(r-a)}$. Hypothesis 3 then fixes $u(a)=z_ie/(4\pi\varepsilon(1+\kappa a))$. Since $r^2\phi'(r)\to0$ for this solution, $\int_a^\infty\rho\,4\pi r^2dr=-4\pi\varepsilon\int_a^\infty(r^2\phi')'dr=4\pi\varepsilon a^2\phi'(a)=-z_ie$. Evaluating $\phi-z_ie/(4\pi\varepsilon r)$ at $r=a$ gives DeVoe's Eq. 10.5.3. DeVoe states decay as $\phi\to0$; the uniqueness class here (bounded $r\phi$) contains the screened solution.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.5, Eqs. 10.5.1–10.5.3 and the definition of $\kappa$ and $I_c$. [Section 10.5](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.05%3A_Derivation_of_the_Debye-Huckel_Theory)
