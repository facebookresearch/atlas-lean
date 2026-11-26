# Backward bifurcation in the two-stage contagion model with renewal

**Model.** A normalized population $S+W+I+R=1$ of susceptibles $S$, weakened individuals $W$, infectious promoters $I$ and inactive individuals $R$ evolves by

$$
\begin{aligned}
S'&=-\beta IS+\gamma W+\eta R, & W'&=(1-\rho)\beta IS-\beta IW-\gamma W,\\
I'&=\beta IW+\rho\beta IS-\alpha I, & R'&=\alpha I-\eta R,
\end{aligned}
$$

with contact rate $\beta>0$, probability $\rho\in(0,1)$ that a contact infects directly (otherwise it weakens), fading rate $\gamma>0$ of weakness, inactivation rate $\alpha>0$ and waning rate $\eta>0$ (second-stage contact rate taken equal to $\beta$). Using $W=1-S-I-R$ gives a three-dimensional system in $(S,I,R)$. Assume $\gamma\ge\alpha$ and set $\kappa=1+\alpha/\eta$.

**Theorem (Theorem 2.1).** The unique disease-free equilibrium $\mathcal E_0=(1,0,0)$ is locally asymptotically stable if $\mathcal R_0=\rho\beta/\alpha<1$ and unstable if $\mathcal R_0>1$.

**Theorem (direction of bifurcation, Theorem 2.2).** Let

$$
\rho^*=\frac{-\alpha+\sqrt{\alpha\gamma\kappa}}{\gamma\kappa-\alpha}.
$$

If $\rho>\rho^*$ the transcritical bifurcation at $\mathcal R_0=1$ is forward; if $\rho<\rho^*$ it is backward.

**Theorem (endemic equilibria, Theorems 2.3–2.4).** If $\rho^*<\rho<1$, there is no endemic equilibrium for $\mathcal R_0\le1$ and a unique one $\mathcal E_+$ for $\mathcal R_0>1$, born stable at $\mathcal R_0=1$. If $0<\rho<\rho^*$, define

$$
\mathcal R_C=\rho(2-\rho)-\rho^2\frac{\gamma\kappa}{\alpha}+\frac{2\rho(1-\rho)}{\alpha}\sqrt{\alpha\gamma\kappa}.
$$

Then there is no endemic equilibrium for $\mathcal R_0<\mathcal R_C$, two endemic equilibria $\mathcal E_\pm$ for $\mathcal R_C\le\mathcal R_0<1$ (coinciding at $\mathcal R_0=\mathcal R_C$, a saddle-node), and a unique one $\mathcal E_+$ for $\mathcal R_0\ge1$; a branch of unstable equilibria $\mathcal E_-$ emerges backward from $\mathcal E_0$ at $\mathcal R_0=1$. An endemic equilibrium is locally asymptotically stable when its characteristic polynomial $\lambda^3+a_2\lambda^2+a_1\lambda+a_0$ satisfies the Routh–Hurwitz conditions $a_2>0$, $a_0>0$, $a_1a_2>a_0$ (Theorem 2.5).

## Expansion

At $\mathcal E_0$ the Jacobian has eigenvalues $-\gamma$, $\rho\beta-\alpha$ and $-\eta$, which gives Theorem 2.1; the weakened route does not enter because $W=0$ at $\mathcal E_0$, so only direct infections ($\rho\beta$ over an infectious period $1/\alpha$) count in $\mathcal R_0$. Eliminating $S$ and $R=\alpha I/\eta$ reduces endemic equilibria to the positive roots of a quadratic $\Phi(I)=a I^2+b(\beta)I+c(\beta)$ with $c<0\iff\mathcal R_0>1$. The sign of $b$ at $\mathcal R_0=1$ decides whether the root leaving $I=0$ is positive for $\mathcal R_0$ slightly above or below $1$; $b>0$ there is equivalent to $\psi(\rho)=(\gamma\kappa-\alpha)\rho^2+2\alpha\rho-\alpha>0$, i.e. $\rho>\rho^*$. The Castillo-Chavez–Song center-manifold criterion confirms the bifurcation direction, and $\mathcal R_C$ is where the discriminant of $\Phi$ vanishes. Numerically, the model with renewal also shows Hopf bifurcations, coexisting stable equilibria and limit cycles.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Sources

- J. Heidecke and M. V. Barbarossa, "When ideas go viral: complex bifurcations in a two-stage transmission model", arXiv:2011.08792 (2020), Section 2 (Theorems 2.1–2.5, definitions of $\rho^*$ and $\mathcal R_C$), <https://doi.org/10.48550/arXiv.2011.08792>.
