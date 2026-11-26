# Basic offspring number of a mating-structured insect pest model

**Model.** Let $I$ be the immature stages (eggs, larvae, pupae), $Y$ the unmated females, $F$ the mated (fertilized) females and $M$ the males of an insect pest. Eggs are laid by mated females at rate $b$ with logistic limitation by the carrying capacity $K$ of immatures; immatures mature at rate $\nu_I$, a fraction $r \in (0,1)$ becoming females; one male can fertilize $\gamma$ females; unmated females become mated at rate $\nu_Y$ when males are abundant and mated females return to the unmated class at rate $\delta$; $\mu_I, \mu_Y, \mu_F, \mu_M$ are mortality rates. All parameters are positive:

$$ \dot I = b\Big(1-\frac IK\Big)F - (\nu_I+\mu_I)I, \quad \dot Y = r\nu_I I - \nu_Y \min\Big\{\frac{\gamma M}{Y},1\Big\} Y + \delta F - \mu_Y Y, \quad \dot F = \nu_Y \min\Big\{\frac{\gamma M}{Y},1\Big\} Y - (\delta+\mu_F)F, \quad \dot M = (1-r)\nu_I I - \mu_M M. $$

In the male-abundance region $Y < \gamma M$ the mating rate is $\nu_Y$ and the system is cooperative on $\{I \le K\}$. Define the basic offspring number

$$ \mathcal N_0 = \frac{b\,r\,\nu_I\,\nu_Y}{(\nu_I+\mu_I)\big((\nu_Y+\mu_Y)(\delta+\mu_F) - \delta\nu_Y\big)}, $$

the spectral radius of the next-generation matrix of the male-abundance system at the trivial equilibrium; note $(\nu_Y+\mu_Y)(\delta+\mu_F) - \delta\nu_Y = \nu_Y\mu_F + \mu_Y(\delta+\mu_F) > 0$.

**Theorem (male-abundance system).** Let $D = (\nu_Y+\mu_Y)(\delta+\mu_F)-\delta\nu_Y$.

1. The male-abundance system defines a positive dynamical system on $\mathbb R^4_+$.
2. If $\mathcal N_0 \le 1$, the trivial equilibrium $TE = 0$ is globally asymptotically stable.
3. If $\mathcal N_0 > 1$, $TE$ is unstable and there is a unique positive equilibrium

$$ I^* = \Big(1-\frac1{\mathcal N_0}\Big)K, \qquad Y^* = \frac{r\nu_I(\delta+\mu_F)}{D}\,I^*, \qquad F^* = \frac{r\nu_I\nu_Y}{D}\,I^*, \qquad M^* = \frac{(1-r)\nu_I}{\mu_M}\,I^*, $$

which is globally asymptotically stable on $\mathbb R^4_+ \setminus \{I = Y = F = 0\}$.

For the full model with the $\min$ mating term, if $\mathcal N_0 > 1$ and the equilibrium lies in the male-abundance region ($Y^* < \gamma M^*$), then the only equilibria are $TE$, which is unstable, and $EE^* = (I^*,Y^*,F^*,M^*)$, which is asymptotically stable.

## Expansion

The infected-like compartments are $I, Y, F$; the next-generation computation gives the product of the probability $\nu_I/(\nu_I+\mu_I)$ of maturing, the female fraction $r$, and the expected number of eggs a newly emerged female lays over her alternating unmated and mated periods, which gives $\mathcal N_0$. Global stability uses monotone-systems theory. The system is cooperative (the off-diagonal Jacobian entries are non-negative on $I \le K$). Order intervals $[a,b]$ with $f(a) \le 0 \le f(b)$ are positively invariant, and a unique equilibrium inside such an interval attracts it. Since $M$ is driven by $I$ alone, the males equilibrate at $M^* = (1-r)\nu_I I^*/\mu_M$. Under male scarcity the analogous system has its own offspring number, and the condition $Y^* < \gamma M^*$ forces its equilibrium back into the male-abundance region.

## Sources

- Roumen Anguelov, Claire Dufourd, Yves Dumont, "Mathematical model for pest-insect control using mating disruption and trapping", arXiv:1608.04880 (2016): Section 2, displayed formula for the basic offspring number (derived in Appendix A), Theorem 1 (male abundance), Theorem 2 (male scarcity) and Theorem 3; monotone-systems tools in Appendix C, Theorems 10–14. <https://doi.org/10.48550/arXiv.1608.04880> Published version: Applied Mathematical Modelling 52 (2017), 437-457, <https://doi.org/10.1016/j.apm.2017.07.060>.
