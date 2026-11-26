# Two-prey-one-predator Lotka–Volterra system with direct prey competition

**Model.** Two prey $u_1, u_2$ compete directly and share one predator $v$. After rescaling (prey carrying capacities and the predator death rate set to $1$), the system has eight positive parameters:

$$
\begin{aligned}
\dot u_1 &= r_1u_1(1 - u_1) - a_{12}u_1u_2 - a_{13}u_1v,\\
\dot u_2 &= r_2u_2(1 - u_2) - a_{21}u_1u_2 - a_{23}u_2v,\\
\dot v &= v\,(a_{31}u_1 + a_{32}u_2 - 1).
\end{aligned}
$$

Set $C_1 = r_1a_{23}$, $C_2 = r_2a_{13}$, $C_3 = a_{12}a_{23}$, $C_4 = a_{21}a_{13}$. The ratio $C_1/C_2$ compares how well each prey withstands predation relative to its growth (apparent competition), while $C_1/C_3 = r_1/a_{12}$ and $C_2/C_4 = r_2/a_{21}$ measure direct competition.

**Theorem.**
1. Solutions starting in $\mathbb{R}^3_+$ are bounded. If $a_{31} + a_{32} < 1$, the predator goes extinct: $v(t) \to 0$.
2. *Predator–prey faces.* On the $(u_1,v)$ face, $E_1 = (1,0,0)$ is globally asymptotically stable if $a_{31} < 1$; if $a_{31} > 1$ the coexistence point $E_{1v} = \big(1/a_{31}, 0, r_1(1 - 1/a_{31})/a_{13}\big)$ exists and is globally asymptotically stable there (symmetrically for $(u_2,v)$ with $a_{32}$).
3. *Prey-only face.* For the competition subsystem: $E_1$ wins if $r_1/a_{12} > 1 > r_2/a_{21}$; $E_2$ wins if $r_1/a_{12} < 1 < r_2/a_{21}$; the coexistence point $E_{12}$ is globally stable if both ratios exceed $1$; and if both are below $1$, $E_{12}$ is a saddle and the system is bistable.
4. *Invasion of boundary states.* $E_1$ is stable in $\mathbb{R}^3_+$ if $r_2 < a_{21}$ and $a_{31} < 1$. $E_{1v}$ is stable in $\mathbb{R}^3_+$ iff $r_2 - a_{21}\bar u_1 - a_{23}\bar v_1 < 0$, which is equivalent to $C_1 - C_2 > (C_1 - C_4)/a_{31}$. $E_{12}$ (when $r_1 > a_{12}$, $r_2 > a_{21}$) is stable in $\mathbb{R}^3_+$ iff additionally $a_{31}\tilde u_1 + a_{32}\tilde u_2 < 1$, where $\tilde u_1 = C_2(C_1 - C_3)/(C_1C_2 - C_3C_4)$ and $\tilde u_2 = C_1(C_2 - C_4)/(C_1C_2 - C_3C_4)$.
5. *Positive equilibrium.* With $D = a_{32}(C_1 - C_4) + a_{31}(C_2 - C_3)$, the interior equilibrium is

$$ u_1^* = \frac{a_{32}(C_1 - C_2) - C_3 + C_2}{D},\quad u_2^* = \frac{C_1 - C_4 - a_{31}(C_1 - C_2)}{D},\quad v^* = \frac{a_{31}C_2(C_1 - C_3) + a_{32}C_1(C_2 - C_4) - C_1C_2 + C_3C_4}{a_{13}a_{23}\,D}, $$

and it is admissible iff $0 < u_1^*, u_2^* < 1$ and $v^* > 0$. When $C_1 > C_3$ and $C_2 > C_4$, a stable $E_{12}$ and an interior equilibrium exclude each other. If $E^*$ exists, its local asymptotic stability is equivalent to three Routh–Hurwitz inequalities; in particular $E^*$ is stable whenever $C_1C_2 > C_3C_4$ and $D > 0$.

Under the symmetry assumption $C_1 > C_2$, the full classification has 56 realizable subcases. The three-species outcome matches the prey-only outcome except in six cases, where the predator reverses competitive exclusion or creates coexistence. This is a mathematical form of Paine's keystone-predator hypothesis. In the subcase that contains Gilpin's parameters, numerics show chaos reached through period doubling.

## Depends on

- [First integral of the Lotka–Volterra system](../lotka-volterra-predator-prey-model/first-integral.md)

## Expansion

Prey densities are eventually at most $1$, and $w = a_{31}u_1/a_{13} + a_{32}u_2/a_{23} + v$ satisfies $\dot w \le M - \min\{r_1,r_2,1\}\,w$, which bounds the predator. Predator extinction when $a_{31} + a_{32} < 1$ holds because prey densities are eventually below $1$, so $\dot v/v \le a_{31} + a_{32} - 1 + o(1) < 0$. Each two-dimensional face is a classical Lotka–Volterra system with Dulac or Lyapunov functions, and each boundary equilibrium is stable in $\mathbb{R}^3_+$ iff the missing species has negative invasion growth rate there. The interior equilibrium solves a $3\times 3$ linear system, and its stability is decided by the Routh–Hurwitz conditions for the community matrix.

## Sources

- Mingchieh Huang and Tinghui Yang, "Direct and Indirect Competition in a Two-Prey-One-Predator System: Global Dynamics, Chaos, and the Paine Conjecture", arXiv:2611.02246 (2026), Section 2 (Lemmas 2.1–2.2, Theorem 2.3, Lemmas 2.4–2.5), Section 3.1 (positive equilibrium), Lemma 4.1, and Section 6, <https://doi.org/10.48550/arXiv.2611.02246>.
