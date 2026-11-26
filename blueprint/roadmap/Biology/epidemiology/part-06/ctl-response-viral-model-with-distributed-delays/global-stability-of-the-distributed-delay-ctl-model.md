# Global stability of the distributed-delay CTL model

**Setting.** Consider the Nowak–Bangham virus–CTL model with distributed infection and production delays, with uninfected cells $x$, infected cells $y$, virus $v$, CTLs $z$, reproduction numbers $R_1<R_0$ and equilibria $E_0$ (uninfected), $E_1$ (infected, no immune response; exists for $R_0>1$) and $E_2$ (infected with CTL response; exists for $R_1>1$), as in [the equilibrium article](equilibria-and-reproduction-numbers-of-the-distributed-delay-ctl-model.md). Call an initial history *infective* if $y(0)+\int_0^{h_1}f_1(\tau)x(-\tau)v(-\tau)d\tau>0$ or $v(0)+\int_0^{h_2}f_2(\tau)y(-\tau)d\tau>0$.

**Theorem.** Exactly one equilibrium is globally asymptotically stable, as follows.

1. If $R_0\le1$, then $E_0$ is globally asymptotically stable.
2. If $R_1\le1<R_0$, then $E_1$ is globally asymptotically stable for all infective histories.
3. If $R_1>1$, then $E_2$ is globally asymptotically stable for all infective histories with $z_0>0$.

The same trichotomy holds for the special case of discrete intracellular delays (Zhu–Zou model), where it upgrades the earlier local stability of the two infected equilibria to global stability. When $R_1>1$, the immune response lowers the infected-cell level and raises the uninfected-cell level compared with $E_1$.

## Expansion

The proofs use Lyapunov functionals built from $g(u)=u-1-\ln u\ge0$ plus delay "memory" terms. For $E_0$ (with $x_0=s/d$),

$$
U_0=\frac{k_d}{k}x_0\,g\!\Big(\frac{x}{x_0}\Big)+y+\frac{v}{N_d}+\frac pqz+k_d\int_0^{h_1}\!f_1(\tau)\!\int_{t-\tau}^{t}\!x(s)v(s)\,ds\,d\tau+\delta\int_0^{h_2}\!f_2(\tau)\!\int_{t-\tau}^{t}\!y(s)\,ds\,d\tau ,
$$

whose derivative is $-\frac{k_dd}{k}x(1-\frac{x_0}{x})^2+\frac{\mu}{N_d}(R_0-1)v-\frac pqbz\le0$ when $R_0\le1$. For $E_1=(x_1^*,y_1^*,v_1^*,0)$,

$$
U_1=\frac{g(x/x_1^*)}{kv_1^*}+\frac{y_1^*\,g(y/y_1^*)}{k_dx_1^*v_1^*}+\frac{v_1^*\,g(v/v_1^*)}{N_d\delta y_1^*}+\frac{p\,z}{k_dx_1^*v_1^*q}
+\int_0^{h_1}\!f_1(\tau)\!\int_{t-\tau}^{t}\!g\Big(\frac{x(s)v(s)}{x_1^*v_1^*}\Big)ds\,d\tau+\int_0^{h_2}\!f_2(\tau)\!\int_{t-\tau}^{t}\!g\Big(\frac{y(s)}{y_1^*}\Big)ds\,d\tau ,
$$

and $U_2$ is the same with $E_2$ in place of $E_1$ and the CTL term replaced by $\frac{pz_2^*}{k_dx_2^*v_2^*q}g(z/z_2^*)$. Using the equilibrium identities ($s=dx^*+kx^*v^*$, $\delta=k_dx^*v^*/y^*$, $\mu=N_d\delta y^*/v^*$), the derivatives reduce to $-c\,x(1-x^*/x)^2$ minus averages of $g$ evaluated at ratios of delayed and current states, plus (for $U_1$) a CTL term of sign $y_1^*-b/q\le0$, which is where $R_1\le1$ enters. LaSalle's invariance principle for functional differential equations then gives global attractivity, and infective histories exclude the boundary invariant sets.

## Depends on

- [Equilibria and reproduction numbers of the distributed-delay CTL model](equilibria-and-reproduction-numbers-of-the-distributed-delay-ctl-model.md)

## Sources

- Yukihiko Nakata, "Global dynamics of cell mediated immunity in viral infection models with distributed delays", arXiv:1008.2518 (2010), Section 3 (main global-stability theorem and Lyapunov functionals) and Section 4 (discrete-delay application), <https://doi.org/10.48550/arXiv.1008.2518>.
