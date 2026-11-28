# Basic offspring number and absence of intrinsic cycles in a two-stage Aedes life-cycle model

**Model.** Let $m(t)$ be the adult female *Aedes aegypti* population and $p(t)$ the pre-adult (aquatic) population, limited by the carrying capacity $C$ of breeding sites:

$$\frac{dm}{dt}=\kappa\zeta\chi\omega\,p-\epsilon m,\qquad \frac{dp}{dt}=\phi\,m\,\psi\Bigl(\frac pC\Bigr)-(\pi+\omega)p ,$$

where $\phi$ is the oviposition rate at low density, $\psi$ is a continuous decreasing saturation function with $\psi([0,1])\subset[0,1]$, $\psi(0)=1$, $\psi(1)=0$, $\omega$ the maturation rate of immatures, $\pi$ their death rate, $\chi$ and $\zeta$ the fractions passing from larva to pupa and from pupa to adult, $\kappa$ the female fraction, and $\epsilon$ the adult death rate. The biological region is $\Omega=\{m\ge0,\ 0\le p\le C\}$.

**Basic offspring number.**

$$R_M=\frac{\kappa\omega\zeta\chi\phi}{\epsilon(\pi+\omega)} ,$$

the expected number of adult females produced by one female over her lifetime at low density: $\phi/\epsilon$ eggs, each maturing with probability $\omega/(\pi+\omega)$ and becoming an adult female with probability $\kappa\zeta\chi$.

**Theorem.**

1. Solutions with $m_0,p_0\ge0$, $m_0+p_0>0$ stay strictly positive for $t>0$, and $\Omega$ is positively invariant (indeed $p<C$ for all $t>0$).
2. If $0<R_M<1$, the only equilibrium in $\Omega$ is $(0,0)$, a locally asymptotically stable node (mosquito extinction).
3. If $R_M>1$, $(0,0)$ is a saddle and there is a unique positive equilibrium $(\tilde m,\tilde p)$, a locally asymptotically stable node, determined by

$$\psi\Bigl(\frac{\tilde p}{C}\Bigr)=\frac1{R_M},\qquad \tilde m=\frac{\kappa\omega\zeta\chi\,\tilde p}{\epsilon}.$$

4. For every $R_M>0$ the system has no periodic orbit in $\Omega$.

Hence seasonal oscillations of mosquito abundance, and of dengue outbreaks, cannot arise from the intrinsic life-cycle dynamics: they must be driven by seasonally varying parameters, temperature acting on the entomological rates and rainfall on the hatchery capacity $C$.

## Expansion

Positivity: multiplying the equations by $p$ and $m$ and adding gives $\frac{d(mp)}{dt}>-(\epsilon+\pi+\omega)mp$, so $mp$ stays positive; at a first time with $p=C$ one would have $\dot p=-(\pi+\omega)C<0$, a contradiction. Setting $\dot m=\dot p=0$ gives $\tilde m=\kappa\zeta\chi\omega\tilde p/\epsilon$ and $\psi(\tilde p/C)=1/R_M$, which has a solution in $(0,C)$ iff $R_M>1$ by monotonicity of $\psi$; the Jacobian at the origin has determinant $\epsilon(\pi+\omega)(1-R_M)$, giving the saddle/node dichotomy. Periodic orbits are excluded by the Bendixson criterion: the divergence $-\epsilon+\frac{\phi m}{C}\psi'(p/C)-(\pi+\omega)$ is strictly negative on $\Omega$.

## Sources

- Emilene Pliego Pliego, Jorge Velázquez-Castro, Andrés Fraguela Collar, "Seasonality on the life cycle of Aedes aegypti mosquito and its statistical relation with dengue outbreaks", Applied Mathematical Modelling 50 (2017), 484–496, <https://doi.org/10.1016/j.apm.2017.06.003>. Published version of arXiv:1605.06430, cited next; locators there refer to the arXiv version.
- E. Pliego Pliego, J. Velázquez-Castro, A. Fraguela-Collar, "Seasonality on the life cycle of Aedes aegypti mosquito and its effects on dengue outbreaks", arXiv:1605.06430 (2016), Section 2 (life-cycle model), Section 3 (basic offspring number, Theorems 1–2 on invariance and equilibria) and the section on existence of periodic solutions (Bendixson theorem). <https://doi.org/10.48550/arXiv.1605.06430>
