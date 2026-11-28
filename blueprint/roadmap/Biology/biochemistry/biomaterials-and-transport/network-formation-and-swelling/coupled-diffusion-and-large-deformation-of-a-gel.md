# Coupled solvent diffusion and large deformation of a gel

Hong, Zhao, Zhou and Suo model a gel as a network whose solvent content changes by diffusion driven by chemical-potential gradients while the network deforms finitely; time is normalized by $L^2/D$ for a sample size $L$.

Fields: the deformation $x(X,t)$ with gradient $F$ ($\det F > 0$), the nominal solvent concentration $C(X,t) > 0$ per unit dry volume, and the osmotic pressure $P(X,t)$. With free energy $W(F, C)$ per dry volume and molecular incompressibility $1 + vC = \det F$,

$$s_{iK} = \frac{\partial W}{\partial F_{iK}} - P H_{iK}\det F, \qquad \mu = \frac{\partial W}{\partial C} + Pv,$$

where $H$ is the inverse transpose of $F$. Solvent moves by the kinetic law and conservation

$$j_i = -\frac{cD}{kT}\frac{\partial \mu}{\partial x_i}, \qquad \frac{\partial C}{\partial t} + \frac{\partial J_K}{\partial X_K} = 0 \quad (r = 0),$$

with $c = C/\det F$, nominal flux $J_K$ related by $j_i = F_{iK}J_K/\det F$, and quasi-static mechanical equilibrium $\partial s_{iK}/\partial X_K = 0$. These are the source's conservation law (its Eq. (6)) with the pump injection rate $r$ set to zero and its force balance (Eq. (4)) with the body force $B_i$ set to zero. A well-posed problem also needs initial data and chemical (flux or chemical potential) and mechanical (displacement or traction) boundary data, as the source specifies for each example.

## Context

Research level. The theory has no intrinsic time or length scale; for a sample of size $L$ the source normalizes time by $L^2/D$ and, with an order-of-magnitude Stokes–Einstein estimate $D \approx 8\times 10^{-10}$ m²/s and $L = 10^{-3}$ m, obtains about $10^3$ s. This is a reference scale, not a predicted relaxation time of any material, and $D$ here is the solvent molecular diffusivity of the model, distinct from effective poroelastic coefficients measured on gels. The source notes that the earlier Tanaka–Fillmore kinetics, based on polymer–solvent friction, was not coupled to large deformation.

## Depends on

- [Gaussian network stretching free energy](gaussian-network-stretching-free-energy.md)
- [Flory–Huggins mixing free energy of a swollen network](flory-huggins-mixing-free-energy-of-a-swollen-network.md)

## Proof depends on

None.

## Expansion

A theorem page should take one of the source's specified boundary-value problems (Section 6, uniaxial creep with fixed in-plane stretch) and prove the short-time $\sqrt t$ penetration and the long-time approach to the new equilibrium, linking to the heat-equation pages, with the dry limit excluded or treated separately. The linearization about a swollen state, giving a diffusion equation with an effective coefficient, needs its own derivation.

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 2: Eqs. (4) and (6) (force balance with body force and conservation with pump injection, both set to zero here); Section 3: Eqs. (16)–(18); Section 4: kinetic law Eq. (25), its nominal form and the remark on Tanaka and Fillmore (1979); Section 5: boundary conditions, normalization by $L^2/D$ and the Stokes–Einstein estimate; Section 6: uniaxial creep example
