# Invasion reproduction number of a periodic epidemic model

**Setting.** Consider $k$ cocirculating infections (pathogens or strains) in an $n$-compartment model $\dot x = f(t, x)$ whose coefficients are $\omega$-periodic in $t$. Fix a set $A \subseteq \{1, \dots, k\}$ of *resident* infections and call the infections in the complement $A^c$ *invading*. Assume an $A$-endemic $\omega$-periodic solution $x^0(t)$ exists: the infections in $A$ persist periodically and every compartment carrying an infection from $A^c$ is empty. Assume also that $x^0$ is asymptotically stable inside the $A^c$-free subspace; without backward bifurcations this requires every basic and invasion reproduction number of the $A$-only subsystem to exceed $1$.

Reclassify every compartment carrying only resident infections as *uninfected*, and call the $m$ compartments carrying at least one infection from $A^c$ (including resident/invader coinfection classes) the *infected* compartments. Linearizing the infected equations at $x^0(t)$ gives

$$\dot y = \bigl(F(t) - V(t)\bigr) y, \qquad y \in \mathbb{R}^m,$$

with $F(t) \ge 0$ the $\omega$-periodic matrix of new $A^c$-infections and $-V(t)$ $\omega$-periodic and cooperative. Assume the periodic next-generation hypotheses hold for this decomposition and that the evolution operator $Y(t, s)$ of $\dot y = -V(t) y$ is exponentially stable.

**Definition.** The overall $A$-endemic invasion reproduction number is the spectral radius

$$\tilde{\mathcal R}_0^{A} = \rho(L), \qquad (L\Gamma)(t) = \int_0^\infty Y(t, t-a)\, F(t-a)\, \Gamma(t-a)\, da,$$

of the next infection operator $L$ on the space of continuous $\omega$-periodic functions $\mathbb{R} \to \mathbb{R}^m$. Removing all invading infections but one, $i \in A^c$, gives the single-pathogen number $\tilde{\mathcal R}_i^{A}$; typically $\tilde{\mathcal R}_0^{A} = \max_{i \in A^c} \tilde{\mathcal R}_i^{A}$. With $k$ infections there are $k \cdot 2^{k-1}$ single-pathogen numbers (one for each infection $i$ and each set $A$ of the other $k - 1$ infections, $A = \varnothing$ giving the basic reproduction numbers).

**Theorem.** Let $W(t, s, \lambda)$ be the evolution operator of the $\omega$-periodic system

$$\dot w = \Bigl(-V(t) + \tfrac{1}{\lambda} F(t)\Bigr) w, \qquad \lambda > 0,$$

and let $\Phi_{F-V}(t)$ be the principal fundamental matrix of $\dot y = (F(t) - V(t))y$.

1. If $\tilde{\mathcal R}_0^{A} > 0$, then $\lambda = \tilde{\mathcal R}_0^{A}$ is the unique positive solution of $\rho\bigl(W(\omega, 0, \lambda)\bigr) = 1$; and $\tilde{\mathcal R}_0^{A} = 0$ if and only if $\rho\bigl(W(\omega, 0, \lambda)\bigr) < 1$ for all $\lambda > 0$.
2. $\tilde{\mathcal R}_0^{A} - 1$ and $\rho\bigl(\Phi_{F-V}(\omega)\bigr) - 1$ have the same sign (both negative, both zero, or both positive).
3. Consequently the $A$-endemic periodic solution $x^0(t)$ is locally asymptotically stable in the full system if $\tilde{\mathcal R}_0^{A} < 1$ and unstable if $\tilde{\mathcal R}_0^{A} > 1$: the invaders cannot, respectively can, establish.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The only change from the basic reproduction number is epidemiological: once resident infections are counted as "uninfected", the $A$-endemic periodic state plays the role of the disease-free periodic state, and the Wang–Zhao threshold theory applies verbatim to the invading compartments. Items 1–2 are the Wang–Zhao characterizations of $\rho(L)$ through the monodromy matrices, and item 3 follows by linearization at the periodic orbit (Floquet theory together with Palmer's nonautonomous Hartman–Grobman theorem). In practice $\Phi_{F-V}$ is rarely available in closed form, so $\tilde{\mathcal R}_0^{A}$ is computed by finding the root $\lambda$ of $\rho(W(\omega, 0, \lambda)) = 1$ numerically, for example by bisection with a numerical integration of the periodic system over one period. Because $x^0(t)$ must exist before $\tilde{\mathcal R}_0^{A}$ is defined, invasion numbers with larger resident sets are built hierarchically from those with smaller ones. Competition (for example cross-immunity) makes an invasion number smaller than the invader's basic reproduction number; facilitation (for example lesions or immunosuppression that favour secondary infections) makes it larger.

## Sources

- C. Mitchell, C. Kribs, "Invasion reproductive numbers for periodic epidemic models", *Infectious Disease Modelling* 4 (2019) 124–141, Section 2.1 (definitions), Section 2.2.2 and Theorems (2.1)–(2.2), Appendix. <https://doi.org/10.1016/j.idm.2019.04.002> (PMC6531838).
- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic environments", *Journal of Dynamics and Differential Equations* 20 (2008) 699–717, Theorems 2.1–2.2. <https://doi.org/10.1007/s10884-008-9111-8>.
