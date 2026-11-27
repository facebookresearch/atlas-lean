# Hopf oscillations from imitation dynamics of household breeding-site control

**Model.** Aquatic mosquitoes $L_v$, adult mosquitoes $A_v$ and the fraction $w \in [0,1]$ of households removing breeding sites evolve by

$$\begin{aligned}
\dot L_v &= rbA_v\Big(1 - \frac{L_v}{K_v(w)}\Big) - (\nu_L + \mu_L)L_v, \qquad K_v(w) = K_{v_{\max}} - w\,(K_{v_{\max}} - K_{v_{\min}}),\\
\dot A_v &= \nu_L L_v - \mu_A A_v,\\
\dot w &= k\,w(1-w)\big(-r_c + r_d\,m\,A_v\big),
\end{aligned}$$

where control lowers the aquatic carrying capacity from $K_{v_{\max}}$ to $K_{v_{\min}}$, $r_c$ is the perceived cost of control and $r_d m A_v$ the perceived risk of not controlling, which grows with mosquito abundance (imitation dynamics with rate $k$). Let

$$N = \frac{\nu_L\, r b}{(\nu_L + \mu_L)\mu_A}, \qquad \alpha = \frac{m\nu_L}{\mu_A}.$$

**Theorem.**
1. *(Boundary equilibria.)* $E_{01} = (0,0,0)$ and $E_{02} = (0,0,1)$ are mosquito-free; for $N > 1$ there are mosquito-positive states $E_{03}$ (no control, $L_v^* = K_{v_{\max}}(1 - 1/N)$, $A_v^* = \frac{\nu_L}{\mu_A}L_v^*$) and $E_{04}$ (full control, the same with $K_{v_{\min}}$). $E_{01}$ is locally asymptotically stable if $N < 1$ and unstable if $N > 1$, $E_{02}$ is always unstable, $E_{03}$ is locally asymptotically stable if $r_c/r_d > \alpha K_{v_{\max}}(1 - 1/N)$ and unstable if $r_c/r_d < \alpha K_{v_{\max}}(1 - 1/N)$, and $E_{04}$ is locally asymptotically stable if $r_c/r_d < \alpha K_{v_{\min}}(1 - 1/N)$ and unstable if $r_c/r_d > \alpha K_{v_{\min}}(1 - 1/N)$.
2. *(Partial engagement.)* An interior equilibrium

$$E_{05} = \left(\frac{\mu_A r_c}{r_d m \nu_L},\ \frac{r_c}{r_d m},\ \frac{K_{v_{\max}} - \frac{\mu_A r_c}{r_d m\nu_L(1 - 1/N)}}{K_{v_{\max}} - K_{v_{\min}}}\right)$$

exists iff $N > 1$ and $\alpha K_{v_{\min}}(1 - 1/N) \le r_c/r_d \le \alpha K_{v_{\max}}(1 - 1/N)$.
3. *(Stability and Hopf bifurcation.)* The Routh–Hurwitz quantity $a_2a_1 - a_0$ at $E_{05}$ has the sign of the quadratic $f(x) = x^2 - Bx + C$ in $x = r_c/r_d$, where

$$B = \alpha\Big(1 - \frac1N\Big)\big(K_{v_{\max}} + K_{v_{\min}}\big),\qquad C = \alpha^2\Big(1 - \frac1N\Big)^2K_{v_{\max}}K_{v_{\min}} + Q\,\alpha\big(K_{v_{\max}} - K_{v_{\min}}\big)\Big(1 - \frac1N\Big),\qquad Q = \frac{\mu_A^2 + rb\nu_L}{k\mu_Ar_d}.$$

 If $B^2 < 4C$, $E_{05}$ is locally asymptotically stable for $\alpha K_{v_{\min}}(1 - 1/N) < r_c/r_d < \alpha K_{v_{\max}}(1 - 1/N)$; if $B^2 \ge 4C$, it is locally asymptotically stable for $r_c/r_d \in \bigl(\alpha K_{v_{\min}}(1 - 1/N), x_1\bigr) \cup \bigl(x_2, \alpha K_{v_{\max}}(1 - 1/N)\bigr)$, where $x_1 \le x_2$ are the roots of $f$, and for $B^2 > 4C$ a Hopf bifurcation occurs at

$$\frac{r_c}{r_d} = \alpha\,\frac{K_{v_{\max}} + K_{v_{\min}}}{2}\Big(1 - \frac1N\Big) \pm \frac{\sqrt{B^2 - 4C}}{2}.$$

So sustained mosquito–behavior oscillations can arise from the feedback alone, without seasonal forcing.

## Depends on

- [Statement of the local Hopf bifurcation theorem on ℝᴺ](../../../systems-biology/three-variable-repressilator/hopf-bifurcation-theorem.md)

## Expansion

With $w$ frozen, the mosquito subsystem is a stage-structured logistic model with threshold $N$ and equilibrium $L_v^* = K_v(w)(1 - 1/N)$. The behavioral equation is a replicator equation whose payoff difference changes sign at $A_v = r_c/(r_d m)$; matching this level with the mosquito equilibrium determines $w^*$, which must lie in $[0,1]$. Linearizing at $E_{05}$ gives a cubic characteristic polynomial $\lambda^3 + a_2\lambda^2 + a_1\lambda + a_0$ with $a_0, a_2 > 0$, so stability is decided by the sign of $a_2a_1 - a_0$, and a simple pair of imaginary eigenvalues crosses the axis where it vanishes.

## Sources

- M. R. Rahman, C. Kottegoda and L. M. Stolerman, "Oscillatory Regimes in a Game-Theoretic Model for Mosquito Population Dynamics under Breeding Site Control", *Mathematical Biosciences* 402 (2026), 109831, Propositions 1, 2, Theorems 1–4 and Eqs. (8)–(9), <https://doi.org/10.1016/j.mbs.2026.109831> (preprint arXiv:2601.05222).
