# External balance of an open gas-liquid contactor

Let differentiable stored solute amounts $n_g,n_l$ in the gas and liquid phases obey the supplied balances

$$n_g' = G_{\mathrm{in}}-G_{\mathrm{out}}-\dot N,\qquad
n_l' = L_{\mathrm{in}}-L_{\mathrm{out}}+\dot N,$$

where $\dot N$ is the interphase solute transfer rate from gas to liquid and the four external quantities are solute flow rates.
Then the interphase transfer cancels:

$$(n_g+n_l)'=G_{\mathrm{in}}+L_{\mathrm{in}}-G_{\mathrm{out}}-L_{\mathrm{out}}.$$

At steady state both accumulation rates vanish and the total entering solute flow equals the total leaving flow. During transients,
a nonzero net external feed changes the total stored solute; for example, a net feed of $1$ in the chosen units gives $(n_g+n_l)'=1$, independently of the
internal transfer. A closed-vessel relaxation theorem additionally needs its specified constitutive transfer law and no external
ports; it is not a consequence of these balances alone and is not asserted for this open model. Design by transfer units is outside
this result.

## Depends on

## Proof depends on

## Sources

- L. Lamm and L. Jarboe, *Chemical Engineering Separations: A Handbook for Students*, LibreTexts, Section 1.4, the solute balance and operating line of an absorber, Equation 9.1, <https://eng.libretexts.org/Bookshelves/Chemical_Engineering/Chemical_Engineering_Separations%3A_A_Handbook_for_Students_(Lamm_and_Jarboe)/01%3A_Chapters/1.04%3A_Absorption_and_Stripping>.
