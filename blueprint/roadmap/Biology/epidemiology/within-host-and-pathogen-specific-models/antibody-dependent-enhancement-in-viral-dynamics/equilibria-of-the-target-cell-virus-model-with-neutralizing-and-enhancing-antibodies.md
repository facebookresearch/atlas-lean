# Equilibria of the target-cell virus model with neutralizing and enhancing antibodies

Extend the basic within-host virus model with target cells $T$, infected cells $I$, free virus $V$ and antibodies $A$:

$$
\dot T=\Lambda-\mu T-\beta(A)VT,\quad \dot I=\beta(A)VT-\delta I,\quad \dot V=\omega I-cV-bAV,\quad \dot A=aVA-\sigma A,\quad \beta(A)=\beta_0+\beta_1A,
$$

with all constants positive. Here $b$ is the average neutralizing power of antibodies, small for weakly neutralizing ones, and $\beta_1\ge0$ measures antibody-dependent enhancement (ADE) of infection. Let

$$
R_0=\frac{\beta_0\omega\Lambda}{c\delta\mu},\qquad V^{is}=(R_0-1)\frac{\mu}{\beta_0},\qquad V^t=\frac\sigma a,
$$

and assume $V^{is}>V^t$, which implies $R_0>1$.

1. The infection-free equilibrium $(\Lambda/\mu,0,0,0)$ is unstable.
2. The antibody-free (immunosuppression) equilibrium has $V=V^{is}$, $I=(R_0-1)\frac{c\mu}{\omega\beta_0}$ and $T=\frac{\delta c}{\omega\beta_0}$, and is unstable.
3. At the immune-controlled equilibrium the antibody equation forces the virus load to $V=V^t=\sigma/a$. The antibody level $A^f$ is the unique positive root of

$$
\omega\beta(A)\Lambda=\delta(c+bA)\big(\mu+\beta(A)V^t\big),
$$

and $T^f=\frac{\delta(c+bA^f)}{\omega\beta(A^f)}$, $I^f=\frac{(c+bA^f)V^t}{\omega}$.
4. Without ADE ($\beta_1=0$) this is the unique stable equilibrium, with $T=\frac{\Lambda}{\mu+\beta_0V^t}$, $I=\frac{\beta_0\Lambda V^t}{\delta(\mu+\beta_0V^t)}$ and $A=\frac{c\,\beta_0(V^{is}-V^t)}{b(\mu+\beta_0V^t)}$.

So the steady viral load $\sigma/a$ is set by the antibody response alone, whatever the neutralizing power. Weak neutralization (small $b$) or ADE ($\beta_1>0$) changes the antibody level and the infected-cell burden needed to hold it, and they leave different immune signatures on the way to clearance or progression.

## Proof sketch

The antibody equation gives $A=0$ or $V=\sigma/a$. On $A=0$ the system is the standard target-cell model, with immunosuppression equilibrium at $V^{is}$; $V^{is}>V^t$ makes the antibody direction unstable there. On $V=V^t$, the $T$ and $I$ equations give $T$ and $I$ in terms of $A$, and the $V$ equation becomes the quadratic for $A$. With $\beta_1=0$ it is linear and gives the explicit $A$. The source prints the antibody-free $T$ with $\mu$ in place of $\omega$, and the $\beta_1=0$ antibody level with $\beta_0$ in the denominator. The formulas above follow directly from the equilibrium equations.

## Sources

- Antoine Danchin, Oriane Pagani-Azizi, Gabriel Turinici and Ghozlane Yahiaoui, "COVID-19 Adaptive Humoral Immunity Models: Weakly Neutralizing Versus Antibody-Disease Enhancement Scenarios", *Acta Biotheoretica* 70 (2022), 23, <https://doi.org/10.1007/s10441-022-09447-1>. Preprint version: arXiv:2207.03222 (2022), model (eq:fullmodelT)–(eq:fullmodelbeta), definition (eq:defR0), Propositions 1–2, <https://doi.org/10.48550/arXiv.2207.03222>.
