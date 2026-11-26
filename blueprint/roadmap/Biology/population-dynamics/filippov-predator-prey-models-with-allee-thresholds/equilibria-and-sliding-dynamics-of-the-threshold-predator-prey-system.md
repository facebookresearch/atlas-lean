# Equilibria and sliding dynamics of the threshold predator-prey system

**Model.** With prey $N(t) \ge 0$, predators $P(t) \ge 0$, Heaviside function $\theta(x) = 1$ for $x > 0$ and $0$ otherwise, and positive parameters $r, K, a, b, m$ and thresholds $N_a, P_a > 0$,

$$\dot N = rN\Big(1 - \frac NK\Big)\theta(N - N_a) - rN\,\theta(N_a - N) - aNP\,\theta(P - P_a), \qquad \dot P = baNP\,\theta(P - P_a) - mP.$$

Prey grow logistically above the Allee threshold $N_a$ and decline exponentially below it; predation operates only when predators exceed $P_a$. The thresholds cut $\mathbb R_+^2$ into $R_1 = \{N > N_a, P > P_a\}$, $R_2 = \{N < N_a, P > P_a\}$, $R_3 = \{N < N_a, P < P_a\}$, $R_4 = \{N > N_a, P < P_a\}$ with smooth fields

$$f_1 = \begin{pmatrix} rN(1 - N/K) - aNP \\ baNP - mP \end{pmatrix},\ f_2 = \begin{pmatrix} -rN - aNP \\ baNP - mP \end{pmatrix},\ f_3 = \begin{pmatrix} -rN \\ -mP \end{pmatrix},\ f_4 = \begin{pmatrix} rN(1 - N/K) \\ -mP \end{pmatrix},$$

and switching boundaries $\Sigma_{(i,j)}$ between adjacent regions. The candidate equilibria are $E_0 = (0,0)$, $E_1 = (K, 0)$ and $E_2 = \big(\tfrac{m}{ab}, \tfrac ra(1 - \tfrac{m}{abK})\big)$.

**Smooth pieces.**

- (Lemma 1, Theorem 2) For $f_1$: $E_2$ exists iff $abK > m$; $E_0$ is a saddle; $E_1$ is locally asymptotically stable if $abK < m$, non-hyperbolic if $abK = m$ and a saddle if $abK > m$; when $abK > m$, $E_2$ is globally asymptotically stable in the open quadrant.
- (Lemma 2, Theorem 3) For $f_2$: the only admissible equilibrium is $E_0$ (the other root $(m/(ab), -r/a)$ has negative predators), and it is globally asymptotically stable in $\mathbb R_+^2$.
- (Lemma 3, Theorem 4) For $f_3$: $E_0$ is the only equilibrium and is globally asymptotically stable.
- (Lemma 4, Theorem 5) For $f_4$: $E_0$ is unstable and $E_1$ is globally asymptotically stable for all initial data with $N(0) > 0$, $P(0) \ge 0$.

**Proposition 1 (sliding).** No switching line has an attracting sliding segment; sliding is only of escaping type, on

$$\Sigma_{e,(1,2)} = \{N = N_a,\ P_a < P < \tfrac ra(1 - \tfrac{N_a}{K})\},\quad \Sigma_{e,(2,3)} = \{\tfrac{m}{ab} < N < N_a,\ P = P_a\},$$
$$\Sigma_{e,(3,4)} = \{N = N_a,\ 0 < P < P_a,\ N_a < K\},\quad \Sigma_{e,(4,1)} = \{N > \max(N_a, \tfrac{m}{ab}),\ P = P_a\}$$

(each set taken where it is non-empty).

**Proposition 2 (pseudo-equilibria).** The escaping sliding flow on $\Sigma_{(2,3)}$ and $\Sigma_{(3,4)}$ has no positive pseudo-equilibrium; $\Sigma_{(1,2)}$ has none except in the degenerate case $N_a = m/(ab)$, where every point of $\Sigma_{e,(1,2)}$ is one. Only $\Sigma_{(4,1)}$ can carry isolated pseudo-equilibria, namely

$$E_{p4}^{\pm} = \Big(\tfrac12\Big(K \pm \sqrt{K^2 - 4KmP_a/(br)}\Big),\ P_a\Big),$$

provided the discriminant is non-negative and the abscissa exceeds $\max(N_a, m/(ab))$.

## Expansion

Linearizing $f_1$ at $E_2$ gives eigenvalues $-\frac{rm}{2abK} \pm i\omega$ with $\omega^2 = mr(1 - \frac{m}{abK}) - \frac{r^2m^2}{4a^2b^2K^2}$, so for typical parameters $E_2$ is a stable focus with natural period $\tau_n = 2\pi/\omega$; global stability on each piece follows from Lyapunov or Dulac-type arguments and from the explicit decoupled dynamics on $R_3$ and $R_4$. A trajectory therefore settles at coexistence while it stays in $R_1$, but once it crosses $N = N_a$ into $R_2$ it is driven to extinction $E_0$, and once it crosses $P = P_a$ into $R_4$ it is driven to the prey-only state $E_1$. Sliding segments follow from the sign test $(f_i \cdot n)(f_j \cdot n) < 0$ on each boundary, with both normal components pointing away from the line in every case, and pseudo-equilibria are zeros of the Filippov convex combination tangent to the line.

## Sources

- S. Gao, S. Poloni, H. Wang, M. Lewis, "Frequency-induced Tipping: Resonance-Driven Tipping in a Threshold Predator-Prey System" (2026), Section 2.1 (model and candidate equilibria), Section 4.1 (Definitions 1 to 6, Lemmas 1 to 4, Theorems 2 to 5, Propositions 1 and 2), <https://doi.org/10.48550/arXiv.2610.39113>.
