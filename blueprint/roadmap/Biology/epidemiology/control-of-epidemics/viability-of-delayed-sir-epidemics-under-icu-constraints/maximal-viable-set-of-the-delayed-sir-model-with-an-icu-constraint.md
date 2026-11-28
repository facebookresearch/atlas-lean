# Maximal forward-invariant and viable sets of a delayed SIR model under an ICU constraint

Fix a recovery rate $\gamma>0$, a natural transmission rate $\beta>0$, a maximal-intervention rate $0<\beta_\star<\beta$, a latency delay $h>0$, and an ICU capacity $0<i_M\le 1$. The controlled delayed SIR model for the susceptible and infected fractions $(s,i)$ is

$$s'(t) = -b(t)\,s(t)\,i(t-h), \qquad i'(t) = b(t)\,s(t)\,i(t-h) - \gamma\, i(t),$$

with measurable control $b(t)\in[\beta_\star,\beta]$ (non-pharmaceutical interventions) and initial history $\phi\in C([-h,0];\mathbb{R}^2)$ in the simplex $T=\{s,i\ge 0,\ s+i\le 1\}$. The ICU constraint requires $i(t)\le i_M$ for all $t\ge 0$; write $C=\{(s,i)\in T: i\le i_M\}$.

For $b\in\{\beta,\beta_\star\}$ let $\Gamma_b:[\gamma/b,\widehat s_b]\to\mathbb{R}_+$ be the decreasing curve in the $(s,i)$ plane obtained as the backward solution of the worst-case system $s' = b\,i_M\,s$, $i' = -b\,i_M\,s + \gamma i$ from $(\gamma/b, i_M)$ until it reaches $i=0$ at $s=\widehat s_b$. Set

$$A = \bigl([0,\tfrac{\gamma}{\beta}]\times[0,i_M]\cap T\bigr) \cup \{(s,i)\in T: s\in[\tfrac{\gamma}{\beta},\widehat s_\beta],\ i\le \Gamma_\beta(s)\},$$

$$B = \bigl([0,\tfrac{\gamma}{\beta_\star}]\times[0,i_M]\cap T\bigr) \cup \{(s,i)\in T: s\in[\tfrac{\gamma}{\beta_\star},\widehat s_{\beta_\star}],\ i\le \Gamma_{\beta_\star}(s)\}.$$

**Theorem.** Consider histories known only to satisfy $\phi(t)\in C$ for all $t\in[-h,0]$.

1. The set of histories with $\phi(0)\in A$ and past in $C$ is forward invariant (the ICU constraint holds for every admissible control), and $A$ is the maximal such set.
2. The set of histories with $\phi(0)\in B$ and past in $C$ is viable (some control keeps the ICU constraint forever), and $B$ is the maximal such set.
3. For every such history with $\phi(0)\in B$, the greedy feedback that applies $b=\beta$ in the interior and, on the boundary pieces $\{i=i_M\}$ and $\{i=\Gamma_{\beta_\star}(s)\}$, the largest rate keeping the velocity tangent to $B$, namely $\min\{\beta, \gamma i_M/(s(0)\,i(-h))\}$ and $\min\{\beta, \beta_\star\, i(0)/i(-h)\}$ respectively, produces closed-loop solutions remaining in $B$.

These sets do not depend on $h$; since $\Gamma_b$ uses the worst-case past value $i(t-h)=i_M$, they lie inside the delay-free viable sets and do not converge to them as $h\to0$ (Remark 4.10).

## Expansion

1. The functional viability theorem for delay differential inclusions (Haddad) says a closed set of histories is viable iff, at every history in it, some admissible velocity lies in the contingent cone of the set.
2. For sets of the form "current state in $K$, past in $C$", only the current state's tangency matters, and the worst case of the unknown delayed term $i(t-h)\in[0,i_M]$ is $i_M$.
3. On $\{i=i_M\}$ with $s\le\gamma/b$ the infected fraction cannot grow; beyond $\gamma/b$ the boundary must follow the worst-case trajectory, which yields $\Gamma_b$ in closed form ($\Gamma_b(s)=c\,s^{\omega}+s/(\omega-1)$ with $\omega=\gamma/(b\,i_M)\ne1$).
4. Maximality: from any state outside $B$, even the strongest intervention $\beta_\star$ with worst-case history drives $i$ above $i_M$.

## Sources

- D. Breda, M. Della Rossa, L. Freddi, *Viability and control of a delayed SIR epidemic with an ICU state constraint*, arXiv:2401.12907 (Section 4.1, Theorem 4.2, Theorem 4.7 and Remark 4.10). <https://doi.org/10.48550/arXiv.2401.12907> Published version: ESAIM: Control, Optimisation and Calculus of Variations 31 (2025) 9, <https://doi.org/10.1051/cocv/2024083>.
