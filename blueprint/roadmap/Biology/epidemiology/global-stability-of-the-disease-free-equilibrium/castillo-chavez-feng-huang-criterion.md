# Castillo-Chavez–Feng–Huang criterion for global stability of the disease-free equilibrium

**Setting.** Split the state of a compartmental epidemic model into uninfected classes
$X \in \mathbb{R}^{p}$ and infected classes $Z \in \mathbb{R}^{q}$, and write it as

$$\frac{dX}{dt} = F(X, Z), \qquad \frac{dZ}{dt} = G(X, Z), \qquad G(X, 0) = 0,$$

on a positively invariant region $\Omega$ where the model makes biological sense. Let
$U_0 = (X^*, 0)$ be the disease-free equilibrium and $\mathcal{R}_0$ the basic reproduction number
obtained from the next-generation matrix at $U_0$. Assume

- **(H1)** for the disease-free subsystem $\dfrac{dX}{dt} = F(X, 0)$, the point $X^*$ is globally
  asymptotically stable;
- **(H2)** $G(X, Z) = A Z - \hat G(X, Z)$ with $\hat G(X, Z) \ge 0$ (componentwise) for all
  $(X, Z) \in \Omega$, where $A = D_Z G(X^*, 0)$ is a Metzler matrix (all off-diagonal entries
  nonnegative).

**Theorem.** If $\mathcal{R}_0 < 1$ and (H1), (H2) hold, then $U_0$ is a globally asymptotically
stable equilibrium of the system in $\Omega$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Local asymptotic stability for $\mathcal{R}_0 < 1$ is the next-generation threshold theorem: with
$A = \mathcal{F} - \mathcal{V}$, $\rho(\mathcal{F}\mathcal{V}^{-1}) < 1$ is equivalent to $A$ being
Hurwitz. For attractivity, (H2) gives the differential inequality $\dot Z \le A Z$; because $A$ is
Metzler, the linear comparison system $\dot{\bar Z} = A \bar Z$ is cooperative and preserves the
order, so $0 \le Z(t) \le \bar Z(t) = e^{A t} Z(0) \to 0$. Once $Z(t) \to 0$, the $X$-equation is
asymptotically autonomous with limit $\dot X = F(X, 0)$, and (H1) together with the theory of
asymptotically autonomous systems gives $X(t) \to X^*$. The condition $\hat G \ge 0$ typically holds
when incidence is bounded by its value at the disease-free state, for example
$\beta S I / N \le \beta I$ or a media-saturated incidence that only reduces contacts; it fails, and
global stability can be lost through a backward bifurcation, when infection itself raises the force
of infection above its linearization. The criterion therefore also rules out backward bifurcation
whenever it applies. In an influenza model with vaccination and media-reduced contact rates
(susceptible, vaccinated, infected, recovered classes, with $X = (S, V, R)$ and $Z = I$), it shows the
disease-free equilibrium is globally asymptotically stable whenever the vaccination reproduction
number satisfies $\mathcal{R}_v < 1$.

## Sources

- C. Castillo-Chavez, Z. Feng, W. Huang, "On the computation of $\mathcal{R}_0$ and its role on
  global stability", in Mathematical Approaches for Emerging and Reemerging Infectious Diseases: An
  Introduction, IMA Volumes in Mathematics and its Applications 125, Springer (2002) 229-250.
- J. M. Tchuenche, N. Dube, C. P. Bhunu, R. J. Smith, C. T. Bauch, "The impact of media coverage on
  the transmission dynamics of human influenza", BMC Public Health 11 (Suppl 1) (2011) S5, Lemma 1,
  conditions (H1)-(H2) and Theorem 2, <https://doi.org/10.1186/1471-2458-11-s1-s5> (PMC3317585).
- P. van den Driessche, J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for
  compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29-48,
  <https://doi.org/10.1016/S0025-5564(02)00108-6>.
