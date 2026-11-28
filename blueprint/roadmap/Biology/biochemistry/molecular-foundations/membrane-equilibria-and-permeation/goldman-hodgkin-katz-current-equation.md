# Goldman–Hodgkin–Katz current equation

Under the constant-field assumption, the steady current density of one ion species through a homogeneous membrane is $I=P z^2F^2\frac{V}{RT}\frac{C_{\mathrm{in}}e^{zFV/RT}-C_{\mathrm{out}}}{e^{zFV/RT}-1}$ with permeability $P=D\beta/a$, using its continuous extension at $V=0$; if both concentrations are positive, its unique zero is the Nernst potential.

**Setting.** An ion species of valence $z\neq0$ crosses a membrane of thickness $a>0$ separating an inside solution (concentration $C_{\mathrm{in}}\ge0$) from an outside solution ($C_{\mathrm{out}}\ge0$) at temperature $T>0$. The membrane voltage $V$ is the inside minus the outside electric potential, and a positive current carries charge from inside to outside. The assumptions, as summarized by Hodgkin and Katz, are:

1. inside the membrane, ions move by diffusion and electrical drift as in free solution (the one-dimensional [Nernst–Planck flux](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-planck-flux.md)), with a constant diffusion coefficient $D>0$ in the membrane, in a steady state;
2. the electric field is constant throughout the membrane (signed outward field $V/a$, magnitude $|V|/a$);
3. the concentrations just inside the two membrane surfaces equal $\beta$ times those in the adjacent solutions, with the same partition coefficient $\beta>0$ at both surfaces;
4. the membrane is homogeneous.

**Statement.** With the permeability coefficient

$$P=\frac{D\,\beta}{a}$$

and $w=zFV/RT$, the current density carried by the ion is

$$I=P\,z^2\frac{F^2V}{RT}\;\frac{C_{\mathrm{in}}\,e^{w}-C_{\mathrm{out}}}{e^{w}-1}=P\,zF\cdot\frac{w}{e^{w}-1}\cdot\big(C_{\mathrm{in}}e^{w}-C_{\mathrm{out}}\big),$$

where the factor $w/(e^w-1)$ is extended by $1$ at $w=0$, so $I(V=0)=PzF\,(C_{\mathrm{in}}-C_{\mathrm{out}})$ (zero when $C_{\mathrm{in}}=C_{\mathrm{out}}$). In SI units $P$ is in m s$^{-1}$, concentrations in mol m$^{-3}$ and $I$ in A m$^{-2}$. If $C_{\mathrm{in}}=C_{\mathrm{out}}=0$ then $I=0$ for every $V$, and if exactly one concentration is zero $I$ has no zero; for $C_{\mathrm{in}},C_{\mathrm{out}}>0$, $I=0$ if and only if $V$ equals the [Nernst potential](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-potential.md) $\frac{RT}{zF}\ln(C_{\mathrm{out}}/C_{\mathrm{in}})$.

Hodgkin and Katz wrote the permeability as $P=uRT\beta/(Fa)$ in terms of a mobility $u$ normalized for monovalent ions; that expression agrees with $D\beta/a$ when $u$ is defined by $u=FD/(RT)$, and it should not be used with another mobility convention (mechanical mobility per molar force, or electrical drift mobility, differ from it by factors of $F$ or $|z|$).

## Context

Graduate physiology and biophysics. The equation underlies the resting potential, ion-selectivity measurements of channels and the analysis of current–voltage rectification. Alvarez and Latorre note that the constant-field assumption is physically reasonable for thin membranes at low ion concentrations; their Appendix B shows that the zero-current (reversal) potential of a membrane permeable only to ions of one sign and valence can be obtained without it, but the current–voltage relation stated here does require it. It is a foundation for quantitative treatments of ion transport across cell membranes; no Artzi-specific result depends on it.

## Depends on

- [One-dimensional Nernst–Planck flux](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-planck-flux.md)
- [Nernst potential of an ion species](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-potential.md)

## Proof depends on

None.

## Expansion

Proof route: with constant field the steady Nernst–Planck equation for the internal concentration $n(x)$, $J=-D\big(n'+\tfrac{zF}{RT}n\phi'\big)$ with $\phi'$ constant and $J$ constant, is a first-order linear ODE with constant coefficients; integrating across $0\le x\le a$ with boundary values $\beta C_{\mathrm{in}}$ and $\beta C_{\mathrm{out}}$ and solving for $J$ gives the current $I=zFJ$ (Alvarez and Latorre, section "The Goldman current equation", Eqs. 11–12, and Appendix A, Eqs. A2–A11). The second form of $I$ is algebraically identical and makes the $V=0$ value and the zero-current condition $C_{\mathrm{in}}e^w=C_{\mathrm{out}}$ immediate.

Remaining decomposition before the page can be marked ready: (i) the solution of the constant-coefficient linear ODE with two boundary values as a lemma; (ii) the sign conventions for $V$, $I$ and the field fixed in a definition page shared with the Nernst–Planck page (which uses $D$, consistent with $P=D\beta/a$).

## Sources

- O. Alvarez and R. Latorre, "The enduring legacy of the 'constant-field equation' in membrane ion transport", *Journal of General Physiology* 149(10) (2017), 911–920; open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC5688357/) (also [rupress.org](https://rupress.org/jgp/article/149/10/911/43579/)), Introduction, Eq. 1 (the constant-field current equation with its sign conventions); section "The Goldman current equation", Eqs. 11–12; section "The Goldman equation for zero-current potential", Eq. 17 (Hodgkin–Katz permeability) and the list of the four Hodgkin–Katz assumptions; Appendix A (Eqs. A2–A11, diffusion-coefficient form) and Appendix B (reversal potential without the constant-field assumption).
- D. E. Goldman, "Potential, impedance, and rectification in membranes", *Journal of General Physiology* (1943); only the PubMed Central landing page was accessible as text ([pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC2142582/)); cited as the original source as reported by Alvarez and Latorre.
