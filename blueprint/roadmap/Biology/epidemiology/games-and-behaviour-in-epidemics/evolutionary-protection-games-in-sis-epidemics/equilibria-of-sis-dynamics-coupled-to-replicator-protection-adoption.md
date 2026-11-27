# Equilibria of SIS dynamics coupled to replicator dynamics of protection adoption

**Model.** In a large population, a fraction $y\in[0,1]$ is infected (SIS: recovery at rate $\gamma$ returns to susceptible). Each individual either adopts protection or not. A protected susceptible has infection risk scaled by $\alpha\in[0,1)$; an unprotected (resp. protected) infected individual transmits at rate $\beta_U$ (resp. $\beta_P$). Protection costs a susceptible $c_P>0$; infected individuals pay $c_{IU}$ or $c_{IP}$; infection costs a loss $L>0$. With $z_S$ and $z_I$ the fractions of susceptible and of infected individuals who stay *unprotected*, and strategies updated by replicator dynamics within each health class,

$$\dot y=\bigl[(1-y)\bigl(z_S+\alpha(1-z_S)\bigr)\bigl(\beta_U z_I+\beta_P(1-z_I)\bigr)-\gamma\bigr]y,$$

$$\dot z_S=z_S(1-z_S)\bigl[c_P-L(1-\alpha)\bigl(\beta_U z_I+\beta_P(1-z_I)\bigr)y\bigr],\qquad \dot z_I=z_I(1-z_I)(c_{IP}-c_{IU}).$$

The cube $[0,1]^3$ is invariant. If $c_{IU}>c_{IP}$, then $z_I\to0$ from every $z_I(0)<1$, so the analysis reduces to $z_I=0$.

**Thresholds.**

$$y^*_U=1-\frac{\gamma}{\beta_P},\qquad y^*_P=1-\frac{\gamma}{\alpha\beta_P},\qquad y^*_{\rm int}=\frac{c_P}{L(1-\alpha)\beta_P},\qquad z^*_{S,\rm int}=\frac{1}{1-\alpha}\Bigl[\frac{\gamma}{\beta_P(1-y^*_{\rm int})}-\alpha\Bigr].$$

**Proposition.** With $z_I=0$ the equilibria are $\mathbf E0=(0,0,0)$, $\mathbf E1=(0,1,0)$, $\mathbf E2=(y^*_U,1,0)$, $\mathbf E3=(y^*_{\rm int},z^*_{S,\rm int},0)$, $\mathbf E4=(y^*_P,0,0)$, and:

1. $\mathbf E0$ always exists and is unstable;
2. $\mathbf E1$ (disease-free, nobody protects) always exists and is locally stable iff $\beta_P<\gamma$;
3. $\mathbf E2$ (endemic, nobody protects) exists iff $\beta_P>\gamma$ and is locally stable iff $y^*_U<y^*_{\rm int}$;
4. $\mathbf E3$ (endemic, partial protection) exists iff $\gamma<\beta_P$ and $y^*_P<y^*_{\rm int}<y^*_U$, and is then locally stable;
5. $\mathbf E4$ (endemic, everyone protects) exists iff $\gamma<\alpha\beta_P$ and is locally stable iff $y^*_P>y^*_{\rm int}$.

For every parameter value exactly one equilibrium is locally stable. In every regime except item 4 (where $\mathbf E3$ exists), on the plane $z_I=0$ it attracts every trajectory with $y(0)>0$ and $0<z_S(0)<1$ (the source's Remark 1, which argues by index theory and so needs $\mathbf E3$ absent). The invariant faces are excluded: from $y(0)=0$, $z_S(0)=1/2$ the trajectory tends to $\mathbf E1$ even when $\mathbf E1$ is unstable. The stable endemic prevalence is $\min\{y^*_U,\max\{y^*_{\rm int},y^*_P\}\}$ when $\beta_P>\gamma$: protection caps prevalence at the cost–benefit level $y^*_{\rm int}$, which is decreasing in protection efficacy.

**Fast behavioral response.** If strategies equilibrate instantly ($z_S=1$ when $y<y^*_{\rm int}$, $z_S=0$ when $y>y^*_{\rm int}$), the switched scalar dynamics started from $y(0)\ne0$ converges monotonically to $0$ if $y^*_U\le0$, to $y^*_U$ if $0<y^*_U<y^*_{\rm int}$, to $y^*_P$ if $y^*_{\rm int}<y^*_P$, and to the sliding mode $y^*_{\rm int}$ if $y^*_P<y^*_{\rm int}<y^*_U$.

## Expansion

On $z_I=0$, $\dot y=0$ forces $y=0$ or $(1-y)(z_S+\alpha(1-z_S))\beta_P=\gamma$; $\dot z_S=0$ forces $z_S\in\{0,1\}$ or $y=y^*_{\rm int}$ (indifference between protecting and not). Combining the cases gives $\mathbf E0$–$\mathbf E4$, and the Jacobian signs give the stability table. Since only $\mathbf E3$ is interior to the square, index theory excludes limit cycles on the plane when $\mathbf E3$ does not exist, and the unique stable equilibrium attracts the interior of the square. The fast-response limit is a Filippov system with discontinuity at $y=y^*_{\rm int}$; when the vector fields on both sides point toward the switching line, trajectories slide along it.

## Sources

- Abhisek Satapathi, Narendra Kumar Dhar, Ashish R. Hota, Vaibhav Srivastava, "Coupled Evolutionary Behavioral and Disease Dynamics Under Reinfection Risk", IEEE Transactions on Control of Network Systems 11 (2024), 795–807, <https://doi.org/10.1109/tcns.2023.3312250>. Published version of arXiv:2209.07348, cited next; locators there refer to the arXiv version.
- A. Satapathi, N. K. Dhar, A. R. Hota, V. Srivastava, "Coupled Evolutionary Behavioral and Disease Dynamics under Reinfection Risk", arXiv:2209.07348 (2022), Section III (coupled SIS–replicator model, Lemma 1, equilibrium thresholds, Proposition 1, Table I and Proposition 2). <https://doi.org/10.48550/arXiv.2209.07348>
