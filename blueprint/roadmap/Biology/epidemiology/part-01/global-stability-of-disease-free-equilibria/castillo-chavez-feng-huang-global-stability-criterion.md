# Castillo-Chavez–Feng–Huang global stability criterion

**Setting.** Write a compartmental epidemic model on a positively invariant set $\Omega$ as

$$\dot X = F(X, Z), \qquad \dot Z = G(X, Z), \qquad G(X, 0) = 0,$$

where $X \in \mathbb{R}^n$ collects the uninfected compartments and $Z \in \mathbb{R}^m$ the infected (latent, infectious, isolated, ...) compartments. Let $U_0 = (X^*, 0)$ be the disease-free equilibrium and $\mathcal{R}_0$ the basic reproduction number from the next-generation matrix at $U_0$.

**Hypotheses.**

- **(H1)** For the disease-free subsystem $\dot X = F(X, 0)$, the point $X^*$ is globally asymptotically stable.
- **(H2)** $G(X, Z) = A Z - \hat G(X, Z)$ with $\hat G(X, Z) \ge 0$ (componentwise) for all $(X, Z) \in \Omega$, where $A = D_Z G(X^*, 0)$ has nonnegative off-diagonal entries (a Metzler matrix).

**Theorem.** If (H1) and (H2) hold and $\mathcal{R}_0 < 1$, then $U_0$ is a globally asymptotically stable equilibrium of the system in $\Omega$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

At the disease-free equilibrium, $A = \mathcal{F} - \mathcal{V}$ where $\mathcal{F} \ge 0$ is the new-infection Jacobian and $\mathcal{V}$ a nonsingular M-matrix; by the van den Driessche–Watmough theorem, $\rho(\mathcal{F}\mathcal{V}^{-1}) < 1$ iff $A$ is Hurwitz, which gives local asymptotic stability. By (H2), $\dot Z \le A Z$ on $\Omega$, and since $A$ is Metzler the linear flow $e^{tA}$ is order preserving, so the comparison principle gives $0 \le Z(t) \le e^{tA} Z(0) \to 0$. The $X$-equation is then asymptotically autonomous with limit system $\dot X = F(X, 0)$, and (H1) together with the theory of asymptotically autonomous systems gives $X(t) \to X^*$.

The condition $\hat G \ge 0$ typically holds when incidence is bounded by its value at the disease-free state, for example $\beta S I / N \le \beta I$ when $S \le N$, or a media-saturated incidence that only reduces contacts. A term such as $\beta I (S^* - S)/N$ is nonnegative only if $S \le S^*$ on $\Omega$, which fails, for example, when treated or vaccinated individuals return to the susceptible class; in such models the disease-free equilibrium can lose global stability through a backward bifurcation, see the [Castillo-Chavez–Song centre-manifold bifurcation theorem](../backward-bifurcation/castillo-chavez-song-centre-manifold-bifurcation-theorem.md). Some applications state the conclusion for $\mathcal{R}_0 \le 1$; the case $\mathcal{R}_0 = 1$ needs a separate argument because the comparison system is then only neutrally stable.

Applications: a monkeypox model (Peter et al.), a malaria model for Nigeria (Collins and Duffy), and an influenza model with vaccination and media-reduced contact rates (Tchuenche et al., with $X = (S, V, R)$ and $Z = I$), where the criterion gives global asymptotic stability of the disease-free equilibrium whenever the vaccination reproduction number satisfies $\mathcal{R}_v < 1$.

## Sources

- C. Castillo-Chavez, Z. Feng, W. Huang, "On the computation of $R_0$ and its role in global stability", in Mathematical Approaches for Emerging and Reemerging Infectious Diseases: An Introduction, IMA Vol. 125, Springer (2002) 229–250, <https://doi.org/10.1007/978-1-4757-3667-0_13>.
- P. van den Driessche, J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.
- O. J. Peter, S. Kumar, N. Kumari, F. A. Oguntolu, K. Oshinubi, R. Musa, "Transmission dynamics of Monkeypox virus: a mathematical modelling approach", Modeling Earth Systems and Environment 8 (2022) 3423–3434, Section "Stability of disease-free equilibrium" (conditions K1–K2, Lemma 1, Theorem 2), <https://doi.org/10.1007/s40808-021-01313-2> (PMC8516625).
- O. C. Collins, K. J. Duffy, "A mathematical model for the dynamics and control of malaria in Nigeria", Infectious Disease Modelling 7 (2022) 728–741, Appendix 1 (Lemma 1 and proof of Theorem 1), <https://doi.org/10.1016/j.idm.2022.10.005>.
- J. M. Tchuenche, N. Dube, C. P. Bhunu, R. J. Smith, C. T. Bauch, "The impact of media coverage on the transmission dynamics of human influenza", BMC Public Health 11 (Suppl 1) (2011) S5, Lemma 1, conditions (H1)–(H2) and Theorem 2, <https://doi.org/10.1186/1471-2458-11-s1-s5> (PMC3317585).
