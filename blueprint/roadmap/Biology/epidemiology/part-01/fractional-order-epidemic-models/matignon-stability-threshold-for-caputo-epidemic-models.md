# Matignon stability threshold for Caputo epidemic models

**Matignon's criterion.** Let $0<\alpha\le 1$, let ${}^{C}D_t^{\alpha}$ be the [Caputo derivative](caputo-fractional-derivative.md) (the ordinary derivative when $\alpha=1$), and let $x^*$ be an equilibrium of the commensurate-order system ${}^{C}D_t^{\alpha}x=f(x)$, $f\in C^1(\mathbb{R}^n)$, with Jacobian $J=Df(x^*)$.

1. The linear system ${}^{C}D_t^{\alpha}y=Jy$ is asymptotically stable if and only if every eigenvalue $\lambda$ of $J$ satisfies

$$
|\arg\lambda|>\frac{\alpha\pi}{2}.
$$

2. If every eigenvalue of $J$ satisfies this sector condition, then $x^*$ is locally asymptotically stable; if some eigenvalue satisfies $|\arg\lambda|<\alpha\pi/2$, then $x^*$ is unstable.
3. For $0<\alpha<1$ the decay in item 1 is algebraic: solutions of the linear system are $O(t^{-\alpha})$, not exponentially small in general. For $\alpha=1$ the condition is the Hurwitz condition $\operatorname{Re}\lambda<0$, and the decay is exponential.

For rational order $\alpha=q/M$ with $\gcd(q,M)=1$, the characteristic equation $\det(s^{\alpha}I-J)=0$ becomes $\det(\mu^{q}I-J)=0$ in $\mu=s^{1/M}$, and the sector condition holds exactly when every root has $|\arg\mu|>\pi/(2M)$.

**Order-independent $R_0$ threshold.** Consider a Caputo compartmental model whose integer-order version ($\alpha=1$) has a disease-free equilibrium $E_0$ with next-generation decomposition $F,V$ and $R_0=\rho(FV^{-1})$, and whose Jacobian $J(E_0)$ is block triangular with the infected-subsystem Jacobian $F-V$ and a Hurwitz uninfected block. Then, for every order $0<\alpha\le 1$,

- if $R_0<1$, every eigenvalue of $J(E_0)$ has negative real part, hence $|\arg\lambda|>\pi/2\ge\alpha\pi/2$, and $E_0$ is locally asymptotically stable;
- if $R_0>1$, $J(E_0)$ has a positive real eigenvalue, hence $\arg\lambda=0<\alpha\pi/2$, and $E_0$ is unstable.

Thus the fractional order changes the transient (algebraic instead of exponential decay when $\alpha<1$) but not the location of the threshold $R_0=1$, which is computed from the same next-generation matrix as for $\alpha=1$.

## Depends on

- [Caputo fractional derivative](caputo-fractional-derivative.md)
- [Well-posedness of Caputo fractional initial value problems](caputo-fractional-initial-value-problem-well-posedness.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

For the linear system with diagonalizable $J$, the Laplace transform gives $\hat y(s)=(s^{\alpha}I-J)^{-1}s^{\alpha-1}y(0)$, and each mode is $E_\alpha(\lambda t^\alpha)$, with the Mittag-Leffler function $E_{\alpha}(z)=\sum_{k\ge0}z^k/\Gamma(\alpha k+1)$. For $0<\alpha<1$, $E_\alpha(\lambda t^\alpha)\to 0$ exactly when $|\arg\lambda|>\alpha\pi/2$, with algebraic tail $\sim -t^{-\alpha}/(\lambda\,\Gamma(1-\alpha))$; when $|\arg\lambda|<\alpha\pi/2$ it grows like $\exp(\lambda^{1/\alpha}t)/\alpha$. At $\alpha=1$, $E_1(\lambda t)=e^{\lambda t}$; for example $y'=-y$, $y(0)=1$ has solution $e^{-t}$. A linearization argument transfers the linear criterion to nonlinear equilibria. The stability sector contains the open left half-plane, so integer-order Hurwitz stability implies stability at every fractional order, and memory can stabilize equilibria whose eigenvalues have small positive real part but large imaginary part, such as unstable foci of the integer-order model; a real positive eigenvalue lies outside the sector for every $\alpha$, so the $R_0=1$ threshold is inherited. For characteristic polynomials of degree up to three, fractional analogues of the Routh–Hurwitz conditions check the argument condition from the coefficients.

In an eight-compartment COVID-19 model with quarantine, isolation and an environmental viral-load class, the characteristic polynomial at $E_0$ factors as $(\lambda+\delta)^2(\lambda+k_3)(\lambda+k_4)(\lambda^4+a_1\lambda^3+a_2\lambda^2+a_3\lambda+a_4)$ with $a_4=k_0k_1k_2m_3(1-R_0)$, and the criterion gives local stability of $E_0$ exactly when $R_0<1$. The same threshold is derived for SEIQR, epithelial-cell infection and treatment models of COVID-19 in Caputo form, and the rational-order form for an Atangana–Baleanu–Caputo COVID-19 model.

## Sources

- D. Matignon, "Stability results for fractional differential equations with applications to control processing", *Computational Engineering in Systems Applications* (IMACS/IEEE-SMC, Lille, 1996), vol. 2, 963–968.
- M. A. Aba Oud, A. Ali, H. Alrabaiah, S. Ullah, M. A. Khan, S. Islam, "A fractional order mathematical model for COVID-19 dynamics with quarantine, isolation, and environmental viral load", *Advances in Difference Equations* 2021 (2021) 106, Theorem 1, Eqs. (15)–(17), <https://doi.org/10.1186/s13662-021-03265-4> (PMC7877321).
- P. A. Naik, M. Yavuz, S. Qureshi, J. Zu, S. Townley, "Modeling and analysis of COVID-19 epidemics with treatment in fractional derivatives using real data from Pakistan", European Physical Journal Plus 135 (2020) 795, Section 3 ($R_0$, Eq. 17; Theorem 3, Eq. 18; Lemma 2, fractional Routh–Hurwitz conditions, Eq. 24), <https://doi.org/10.1140/epjp/s13360-020-00819-5> (PMC7594999).
- Z. Zhang, A. Zeb, O. F. Egbelowo, V. S. Erturk, "Dynamics of a fractional order mathematical model for COVID-19 epidemic", Advances in Difference Equations 2020 (2020) 420, Theorems 1–4, <https://doi.org/10.1186/s13662-020-02873-w> (PMC7427275).
- A. N. Chatterjee, B. Ahmad, "A fractional-order differential equation model of COVID-19 infection of epithelial cells", Chaos, Solitons and Fractals 147 (2021) 110952, Theorems 1–3, <https://doi.org/10.1016/j.chaos.2021.110952> (PMC8086832).
- M. Awais, F. S. Alshammari, S. Ullah, M. A. Khan, S. Islam, "Modeling and simulation of the novel coronavirus in Caputo derivative", Results in Physics (2020), Theorem 0.3 (Eq. 15, sector condition), <https://doi.org/10.1016/j.rinp.2020.103588> (PMC7671651).
- X.-P. Li, H. A. Bayatti, A. Din, A. Zeb, "A vigorous study of fractional order COVID-19 model via ABC derivatives", Results in Physics (2021), Theorem 1 (rational-order sector condition), <https://doi.org/10.1016/j.rinp.2021.104737> (PMC8401151).
