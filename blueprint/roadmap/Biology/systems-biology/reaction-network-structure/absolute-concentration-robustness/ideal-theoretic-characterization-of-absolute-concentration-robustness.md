# Ideal-theoretic characterization of absolute concentration robustness

Let $(G,\kappa)$ be a mass-action system with species $X_1,\dots,X_n$ and ODEs $\dot x=f_\kappa(x)$; its **steady-state ideal** is $I(G,\kappa)=\langle f_\kappa(x)_1,\dots,f_\kappa(x)_n\rangle\subseteq\mathbb R[x]$ and its positive steady-state locus is $V_{>0}(I)=\{x\in\mathbb R^n_{>0}: f_\kappa(x)=0\}$. The system has **absolute concentration robustness (ACR)** in $X_i$ with ACR-value $\alpha>0$ if $x^*_i=\alpha$ for every positive steady state $x^*$ (Shinar-Feinberg).

**Basic criterion.** $(G,\kappa)$ has ACR in $X_i$ iff $x_i-\alpha$ lies in the vanishing ideal of $V_{>0}(I)$ for some $\alpha>0$; equivalently iff $V_{\mathbb R}$ of the positive part lies in the hyperplane $\{x_i=\alpha\}$, iff every real connected component of that real variety does.

**Sufficient conditions that are not necessary.** ACR in $X_i$ holds if (1) $x_i-\alpha\in I$ for some $\alpha>0$; or (2) $x_i-\alpha\in I:(x_1\cdots x_n)^\infty$ (saturation); or (3) some $g\in I\cap\mathbb R[x_i]$ has a unique positive root. Examples show none of these is necessary, so membership tests in $I$ or its saturation are incomplete deciders.

**Positive-restriction ideal.** For rational $\kappa\in\mathbb Q^r_{>0}$ set

$$J(G,\kappa)=\big\langle f_\kappa(x)_1,\dots,f_\kappa(x)_n,\ x_1z_1^2-1,\dots,x_nz_n^2-1\big\rangle\subseteq\mathbb Q[x,z].$$

The projection $(x;z)\mapsto x$ is a $2^n$-to-1 surjection $V_{\mathbb R}(J)\to V_{>0}(I)$ (a real Rabinowitsch trick).

**Theorem (rational ACR and the real radical).** For $\kappa\in\mathbb Q^r_{>0}$ and $\alpha\in\mathbb Q_{>0}$, ACR in $X_i$ with value $\alpha$ $\iff$ $x_i-\alpha$ vanishes on $V_{>0}(I)$ $\iff$ $x_i-\alpha\in\sqrt[\mathbb R]{J(G,\kappa)}$.

**Theorem (decidable case).** Suppose $J=Q_1\cap Q_2$ with $V_{\mathbb R}(Q_2)=\varnothing$ and $Q_1=\bigcap_{i=1}^\ell P_i$ with each $V_{\mathbb R}(P_i)\ne\varnothing$, and suppose each $P_i$ remains prime over $\mathbb R$ and has a non-singular real zero. Then $(G,\kappa)$ has ACR in $X_j$ with value $\alpha$ iff $x_j-\alpha\in Q_1$, a test performed by Gröbner bases.

## Depends on

- [Chemical reaction network theory](../../chemical-reaction-network-theory/README.md)

## Expansion

Every positive steady state lifts to $2^n$ real points of $V(J)$ via $z_i=\pm x_i^{-1/2}$, so a polynomial vanishes on $V_{>0}(I)$ iff it vanishes on $V_{\mathbb R}(J)$; the Real Nullstellensatz identifies the latter vanishing ideal with the real radical $\sqrt[\mathbb R]J$, which is why rationality of $\alpha$ is needed (an irrational ACR value such as $\sqrt{\kappa_1/\kappa_2}$ shows up as its minimal polynomial instead). Real radicals are hard to compute in general, but a prime ideal with a non-singular real zero is real (equals its real radical), which gives the decidable case after discarding components with no real points. Complementary tools are a Gröbner-cover procedure for zero-divisor ACR, where $x_i-\alpha$ multiplied by a non-vanishing factor lies in the ideal for generic parameters, and numerical irreducible decomposition plus dense real sampling of each connected component, which can certify or preclude ACR when symbolic computation is infeasible.

## Sources

- L. D. García Puente, E. Gross, H. A. Harrington, M. Johnston, "Absolute concentration robustness: algebra and geometry", *Journal of Symbolic Computation* 128 (2025), 102398, Section 2.4 (Propositions 2.15, 2.20), Section 3 (Propositions 3.7, 3.8, 3.22, 3.27, Lemmas 3.20, 3.25, Theorem 3.28), Section 4 and Section 5 (Proposition 5.2, Corollary 5.3, Proposition 5.4), <https://doi.org/10.1016/j.jsc.2024.102398> (preprint arXiv:2401.00078).
