# Delay destabilization of activator–inhibitor steady states

**Setting.** Consider a two-component regulatory system $\dot x = f(x)$ whose components are monotone in each regulator (each interaction is purely activating or purely inhibiting) and whose solutions are bounded, and introduce a delay $\tau \ge 0$ in one cross-regulation, e.g. $\dot x_1 = f_1(x_1, x_2(t-\tau))$, $\dot x_2 = f_2(x_1, x_2)$. At a fixed point $x^*$ with Jacobian entries $a_{ij}$ the characteristic equation is

$$\Delta(\lambda, \tau) = (\lambda - a_{11})(\lambda - a_{22}) - a_{12}a_{21}e^{-\lambda\tau} = 0.$$

An **activator–inhibitor oscillator** has signed Jacobian $\begin{pmatrix} + & - \\ + & - \end{pmatrix}$ at $x^*$: self-activation $a_{11} > 0$, self-decay $a_{22} < 0$, and a negative loop $a_{12}a_{21} < 0$ (the substrate-depletion oscillator, $\begin{pmatrix} - & - \\ + & + \end{pmatrix}$, is analogous).

**Theorem.**
1. If $x^*$ is stable for $\tau = 0$ and the signed Jacobian is of activator–inhibitor (or substrate-depletion) type, then increasing $\tau$ eventually destabilizes $x^*$: there is a threshold $\tau^*$ with $x^*$ unstable for $\tau > \tau^*$. In particular, when $x^*$ is the only fixed point and lies between the extrema of the activator nullcline ($a_{11} > 0$), a sufficiently long delay yields sustained oscillations.
2. For a single negative feedback loop $x_1 \to x_2 \to \cdots \to x_n \to x_1$ (product of edge signs negative) with one delayed interaction, the fixed point is unique, and every Hopf bifurcation produced by increasing $\tau$ is a loss of stability: at the crossing $\lambda = i\omega$, $\operatorname{Re}\,\frac{d\lambda}{d\tau} > 0$. Hence an unstable fixed point cannot be stabilized by a delay, and when the fixed point is destabilized a stable limit cycle exists.

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

For part 1, view roots of $\Delta$ as intersections of the parabola $p(\lambda) = (\lambda - a_{11})(\lambda - a_{22})$ with $q(\lambda) = a_{12}a_{21}e^{-\lambda\tau}$, which for $a_{12}a_{21} < 0$ is negative, increasing and tends to $0$ exponentially in $\lambda$. As $\tau \to \infty$, $q \to 0$ uniformly on $\operatorname{Re}\lambda \ge \delta > 0$, so by continuity (Rouché) a root approaches the positive zero $a_{11}$ of $p$, and $x^*$ cannot remain stable. Typically the two stable real roots first merge into a complex pair whose real part increases through zero (a Hopf bifurcation) and later split again into real roots tending to $a_{11}$ and $a_{22}$. Since eigenvalues depend continuously on $\tau$ and every delay-driven crossing is from left to right, the first crossing is a Hopf bifurcation, and the Poincaré–Bendixson theorem in two dimensions (and its extension to monotone cyclic feedback systems for the single loop) turns local instability of the unique fixed point into global convergence to a periodic orbit. Without delay, two-component systems need autocatalysis for oscillations; the delay replaces the required time-scale separation.

## Sources

- N. Radde, "The impact of time delays on the robustness of biological oscillators and the effect of bifurcations on the inverse problem", EURASIP Journal on Bioinformatics and Systems Biology 2009 (2009) 327503, Eqs. (2)–(8), Theorems 1–2, Corollary 1 and Appendices A–C, <https://doi.org/10.1155/2009/327503>, PMCID PMC3192793.
