# Bistability from autophosphorylation at a single site

A protein has an unphosphorylated form X (concentration $x$) and a phosphorylated form Y ($y$). X phosphorylates itself in trans ($2X \to X + Y$, rate $k_1$), Y phosphorylates X ($X + Y \to 2Y$, rate $k_8$), an external kinase E phosphorylates X through a complex XE ($d$), and a phosphatase F dephosphorylates Y through a complex YF ($c$):

$$

\begin{aligned}
\dot x &= -k_1x^2 + k_4 c - k_5 e x + k_6 d - k_8 x y, & \dot d &= k_5 e x - (k_6+k_7)d, & \dot e &= -k_5 e x + (k_6+k_7)d,\\
\dot c &= k_2 f y - (k_3+k_4)c, & \dot f &= -k_2 f y + (k_3+k_4)c, & \dot y &= k_1x^2 - k_2 f y + k_3 c + k_7 d + k_8 x y,
\end{aligned}

$$

with conserved totals $A = x + y + c + d$ of the substrate, $B = c + f$ of phosphatase and $C = d + e$ of kinase. With no external kinase ($C = 0$) and the Michaelis–Menten reduction for the phosphatase ($K_{M1} = (k_3+k_4)/k_2$), the dynamics reduce to the scalar equation

$$

y' = k_1(A-y)^2 + k_8(A-y)\,y - \frac{B k_4\, y}{K_{M1} + y}.

$$

**Theorem.** Let $\alpha = k_8/k_1$.

1. If $\alpha > 2$, $A^2 k_1 < B k_4$, $k_8$ is sufficiently large and $K_{M1}$ sufficiently small (other parameters fixed), the scalar equation has three hyperbolic steady states, two asymptotically stable and one unstable; they arise in a generic cusp bifurcation.
2. For the full mass-action system with $d = e = 0$, $C = 0$ and fixed totals $A, B$, there are parameters with three steady states, two asymptotically stable and one a hyperbolic saddle, again from a generic cusp bifurcation; for all parameters every solution converges to a steady state, so there are no periodic solutions.
3. With an external kinase present ($C > 0$) but without the $X + Y \to 2Y$ reaction ($k_8 = 0$), positive steady states correspond to roots of a degree-6 polynomial in $(0,x_{\max})$, and there are parameters with three positive steady states.

So autophosphorylation alone is enough to make a single phosphorylation site bistable, which is impossible for the same site under ordinary Michaelis–Menten kinase and phosphatase action.

## Expansion

Positive steady states of the scalar equation are roots in $(0,A)$ of a cubic $p_3(y)$ obtained by clearing the denominator. A cubic $ay^3 + by^2 + cy + d$ has a triple root iff $b^3 = 27a^2 d$ and $c^3 = 27ad^2$; choosing parameters at a triple root and checking the nondegeneracy conditions gives a generic cusp, from which three roots unfold. The conditions $\alpha > 2$ and $A^2k_1 < Bk_4$ make the autocatalytic term strong enough and the phosphatase saturable enough for the sign pattern needed by three positive roots. Convergence of the full system follows from geometric singular perturbation and a monotonicity argument for the reduced flow.

## Sources

- Lisa Maria Kreusser, Alan D. Rendall, "Autophosphorylation and the dynamics of the activation of Lck", arXiv (2021); Bulletin of Mathematical Biology (2021). Section 2 (basic model and its reduction), Section 3 (Theorems 1–3), Section 4 (Lemma 2, Theorem 4). <https://doi.org/10.48550/arXiv.2101.09295>. Published version: Bulletin of Mathematical Biology 83(6) (2021), article 64, <https://doi.org/10.1007/s11538-021-00900-9>; locators above refer to the arXiv version.
