# Matignon stability threshold for Caputo epidemic models

**Matignon's criterion.** Let $0<\alpha\le 1$ and let $x^*$ be an equilibrium of the commensurate-order Caputo system ${}^{C}D_t^{\alpha}x=f(x)$, $f\in C^1(\mathbb{R}^n)$, with Jacobian $J=Df(x^*)$. If every eigenvalue $\lambda$ of $J$ satisfies
$$
|\arg\lambda|>\frac{\alpha\pi}{2},
$$
then $x^*$ is locally asymptotically stable; if some eigenvalue satisfies $|\arg\lambda|<\alpha\pi/2$, then $x^*$ is unstable. For rational order $\alpha=q/M$ with $\gcd(q,M)=1$ the condition is equivalently stated on the roots of $\det(\mu^{q}I-J)=0$ in the variable $\mu=\lambda^{1/M}$: stability holds when every root has $|\arg\mu|>\pi/(2M)$.

**Order-independent $R_0$ threshold.** Consider a Caputo compartmental model whose integer-order version ($\alpha=1$) has a disease-free equilibrium $E_0$ with next-generation decomposition $F,V$ and $R_0=\rho(FV^{-1})$. Then, for every order $0<\alpha\le 1$,

- if $R_0<1$, every eigenvalue of $J(E_0)$ has negative real part, hence $|\arg\lambda|>\pi/2\ge\alpha\pi/2$, and $E_0$ is locally asymptotically stable;
- if $R_0>1$, $J(E_0)$ has a positive real eigenvalue, hence $\arg\lambda=0<\alpha\pi/2$, and $E_0$ is unstable.

Thus the fractional order changes the transient (algebraic instead of exponential decay) but not the location of the threshold $R_0=1$. In the source's eight-compartment COVID-19 model with quarantine, isolation and an environmental viral-load class $M$, the characteristic polynomial at $E_0$ factors as $(\lambda+\delta)^2(\lambda+k_3)(\lambda+k_4)(\lambda^4+a_1\lambda^3+a_2\lambda^2+a_3\lambda+a_4)$ with $a_4=k_0k_1k_2m_3(1-R_0)$, and the criterion gives local stability of $E_0$ exactly when $R_0<1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Well-posedness of Caputo fractional initial value problems](caputo-fractional-initial-value-problem-well-posedness.md)

## Expansion

For the linear system ${}^{C}D_t^{\alpha}y=Jy$, diagonalization reduces each mode to $y(t)=E_\alpha(\lambda t^\alpha)y(0)$, and $E_\alpha(\lambda t^\alpha)\to 0$ exactly when $|\arg\lambda|>\alpha\pi/2$; this is Matignon's theorem, and a linearization argument transfers it to the nonlinear equilibrium. The stability sector $|\arg\lambda|>\alpha\pi/2$ contains the open left half-plane, so integer-order Hurwitz stability implies stability at every fractional order, while a positive real eigenvalue lies outside the sector for every $\alpha$. Combining this with the integer-order fact that $J(E_0)$ is Hurwitz iff $R_0<1$ yields the order-independent threshold.

## Sources

- M. A. Aba Oud, A. Ali, H. Alrabaiah, S. Ullah, M. A. Khan, S. Islam, "A fractional order mathematical model for COVID-19 dynamics with quarantine, isolation, and environmental viral load", *Advances in Difference Equations* 2021 (2021) 106. <https://doi.org/10.1186/s13662-021-03265-4>. PMCID: PMC7877321. (Theorem 1, Eq. (15)–(17).)
- D. Matignon, "Stability results for fractional differential equations with applications to control processing", *Computational Engineering in Systems Applications* (IMACS/IEEE-SMC, Lille, 1996), vol. 2, 963–968.
