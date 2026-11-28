# Phage therapy model with resistance and innate immunity

Let $S$ and $R$ be phage-sensitive and phage-resistant bacteria, $P_S$ and $P_R$ phages specific to each, and $I$ the innate immune response. With per-capita lysis rate $F(P)=\phi P/(1+P/P_C)$, the model is

$$\dot S=rS\Bigl(1-\frac{S+R}{K_C}\Bigr)(1-\mu)-SF(P_S)-\frac{\epsilon IS}{1+(S+R)/K_D},$$

$$\dot R=r'R\Bigl(1-\frac{S+R}{K_C}\Bigr)+\mu rS\Bigl(1-\frac{S+R}{K_C}\Bigr)-RF(P_R)-\frac{\epsilon IR}{1+(S+R)/K_D},$$

$$\dot P_S=\beta SF(P_S)-\phi SP_S-\omega P_S+\rho_S(t),\qquad \dot P_R=\beta RF(P_R)-\phi RP_R-\omega P_R+\rho_R(t),$$

$$\dot I=\alpha I\Bigl(1-\frac{I}{K_I}\Bigr)\frac{S+R}{S+R+K_N},$$

with injection rates constrained by $\rho_S,\rho_R\ge0$ and $\rho_S+\rho_R\le\rho_{\max}$. Here $\mu$ is the per-division mutation probability to resistance, $\beta$ the burst size and $\omega$ the phage decay rate. In the dimensionless variables $x=(S/K_D,\,R/K_D,\,P_S/P_C,\,I/K_I,\,P_R/P_C)$ with controls $u_1=\rho_S/\rho_{\max}$, $u_2=\rho_R/\rho_{\max}$, $q=\rho_{\max}/P_C$, $k_{CD}=K_C/K_D$, $\psi=\phi K_D$ and scaled infection rate $\mathcal I(z)=\psi z/(1+z)$, the phage equations read $\dot x_3=\beta x_1\mathcal I(x_3)-\psi x_1x_3-\omega x_3+qu_1$ (and likewise for $x_5$ with $x_2$, $u_2$), and the controls lie in $U=\{u\in\mathbb{R}_+^2:u_1+u_2\le1\}$.

**Positive invariance.** For every measurable control with values in $U$, the set

$$\Omega=\Bigl\{x\in\mathbb{R}_+^5:\ x_1+x_2\le k_{CD},\ x_3\le\frac{q+\beta\psi k_{CD}}{\omega},\ x_4\le1,\ x_5\le\frac{q+\beta\psi k_{CD}}{\omega}\Bigr\}$$

is positively invariant for the scaled system.

## Depends on

This node has no prerequisites.

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Nonnegativity holds because each right-hand side is nonnegative on the corresponding coordinate face. Dropping the nonpositive lysis, killing and $(1-\mu)$ losses gives $\dot x_1+\dot x_2\le(rx_1+r'x_2)(1-(x_1+x_2)/k_{CD})$, so $x_1+x_2$ cannot cross $k_{CD}$; the logistic immune equation keeps $x_4\le1$. Then $\mathcal I(x_3)\le\psi$, $u_1\le1$ and $x_1\le k_{CD}$ give $\dot x_3\le(\beta\psi k_{CD}+q)-\omega x_3$, which bounds $x_3$, and the same for $x_5$.

## Sources

- G. Li, C. Y. Leung, Y. Wardi et al., *Optimizing the timing and composition of therapeutic phage cocktails: a control-theoretic approach*, Bulletin of Mathematical Biology 82 (2020), article 75, <https://doi.org/10.1007/s11538-020-00751-w> (PMCID: PMC8272981). Section 2.1, equations (1)–(13), and Section 3.1, Proposition 1.
