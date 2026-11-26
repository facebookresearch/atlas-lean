# Castillo-Chavez–Feng–Huang global stability criterion

**Setting.** Write a compartmental epidemic model on a positively invariant set $\Omega$ as
$$\dot X = F(X, Z), \qquad \dot Z = G(X, Z), \qquad G(X, 0) = 0,$$
where $X \in \mathbb{R}^n$ collects the uninfected compartments and $Z \in \mathbb{R}^m$ the infected (latent, infectious, isolated, ...) compartments. Let $U_0 = (X^*, 0)$ be the disease-free equilibrium and $\mathcal{R}_0$ the basic reproduction number from the next-generation matrix at $U_0$.

**Hypotheses.**

- **(H1)** For the disease-free subsystem $\dot X = F(X, 0)$, the point $X^*$ is globally asymptotically stable.
- **(H2)** $G(X, Z) = A Z - \hat G(X, Z)$ with $\hat G(X, Z) \ge 0$ (componentwise) for all $(X, Z) \in \Omega$, where $A = D_Z G(X^*, 0)$ has nonnegative off-diagonal entries (a Metzler matrix, i.e. $-A$ is a Z-matrix).

**Theorem.** If (H1) and (H2) hold, then $U_0$ is a globally asymptotically stable equilibrium in $\Omega$ provided $\mathcal{R}_0 < 1$ (and it is locally asymptotically stable for $\mathcal{R}_0 < 1$ in any case).

## Expansion

At the disease-free equilibrium, $A = \mathcal{F} - \mathcal{V}$ where $\mathcal{F} \ge 0$ is the new-infection Jacobian and $\mathcal{V}$ a nonsingular M-matrix; by the van den Driessche–Watmough theorem, $\rho(\mathcal{F}\mathcal{V}^{-1}) < 1$ iff the spectral abscissa of $A$ is negative. By (H2), $\dot Z \le A Z$ on $\Omega$, and since $A$ is Metzler the linear flow $e^{tA}$ is order preserving, so the comparison principle gives $0 \le Z(t) \le e^{tA} Z(0) \to 0$. The $X$-equation is then asymptotically autonomous with limit system $\dot X = F(X, 0)$, and (H1) together with the theory of asymptotically autonomous systems gives $X(t) \to X^*$. The typical obstacle to (H2) is a term such as $\beta I (S^* - S)/N$: it is nonnegative only if $S \le S^*$ on $\Omega$ (and if $N$ is constant or bounded appropriately), which fails, for example, when treated or vaccinated individuals return to the susceptible class; in such models a backward bifurcation may occur instead, see the Castillo-Chavez–Song centre-manifold criterion (backward-bifurcation-at-the-epidemic-threshold topic). Some applications state the conclusion for $\mathcal{R}_0 \le 1$; the case $\mathcal{R}_0 = 1$ needs a separate argument because the comparison system is then only neutrally stable.

## Sources

- O. J. Peter, S. Kumar, N. Kumari, F. A. Oguntolu, K. Oshinubi, R. Musa, "Transmission dynamics of Monkeypox virus: a mathematical modelling approach", Modeling Earth Systems and Environment 8 (2022) 3423–3434, Section "Stability of disease-free equilibrium" (conditions K1–K2, Lemma 1, Theorem 2), <https://doi.org/10.1007/s40808-021-01313-2> (PMC8516625).
- O. C. Collins, K. J. Duffy, "A mathematical model for the dynamics and control of malaria in Nigeria", Infectious Disease Modelling 7 (2022) 728–741, Appendix 1 (Lemma 1 and proof of Theorem 1), <https://doi.org/10.1016/j.idm.2022.10.005>.
- C. Castillo-Chavez, Z. Feng, W. Huang, "On the computation of $R_0$ and its role in global stability", in Mathematical Approaches for Emerging and Reemerging Infectious Diseases: An Introduction, IMA Vol. 125, Springer (2002) 229–250, <https://doi.org/10.1007/978-1-4757-3667-0_13>.
