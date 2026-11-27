# Ulam–Hyers stability of fractional-order compartmental models

Let $P : [0,\tau] \to \mathbb R^n$ be the vector of compartments of an epidemic model written as the Caputo initial value problem

$$ {}^{C}D^{\vartheta}_{0^+} P(t) = Z(t, P(t)), \qquad P(0) = P_0, \qquad 0 < \vartheta \le 1, $$

on the Banach space $\mathcal X = C([0,\tau]; \mathbb R^n)$ with the sup norm, where $Z$ is continuous and globally Lipschitz in $P$ with constant $L_Z$. Solutions are exactly the fixed points of

$$ (\mathcal T P)(t) = P_0 + \frac{1}{\Gamma(\vartheta)} \int_0^t (t-r)^{\vartheta - 1} Z(r, P(r))\,dr. $$

The problem is **Ulam–Hyers stable** if there is $C > 0$ such that for every $\zeta > 0$ and every $V \in \mathcal X$ with $V(0) = P_0$ and $\big|{}^{C}D^{\vartheta}_{0^+} V(t) - Z(t, V(t))\big| \le \zeta$ on $[0,\tau]$ (a $\zeta$-approximate solution), there is a solution $\bar V$ with $\|V - \bar V\| \le C\zeta$. It is *generalized* Ulam–Hyers stable if $C\zeta$ is replaced by $\varphi(\zeta)$ for a continuous $\varphi$ with $\varphi(0) = 0$.

**Theorem.** Let $a = \tau^{\vartheta}/\Gamma(\vartheta + 1)$. If $a L_Z < 1$, then:
1. $\mathcal T$ is a contraction, so the model has a unique solution on $[0,\tau]$;
2. every $\zeta$-approximate solution $V$ satisfies $\|V - \mathcal T V\| \le a\zeta$;
3. the model is Ulam–Hyers stable with constant $C = \dfrac{a}{1 - aL_Z}$, and hence generalized Ulam–Hyers stable.

The same argument applies to the Atangana–Baleanu–Caputo derivative of order $k \in (0,1]$, whose integral operator is $\frac{1-k}{AB(k)} f(t) + \frac{k}{AB(k)\Gamma(k)}\int_0^t (t-s)^{k-1} f(s)\,ds$ with $AB(k) = 1 - k + k/\Gamma(k)$: replacing $a$ by $a_{AB} = \frac{1-k}{AB(k)} + \frac{\tau^{k}}{AB(k)\Gamma(k)}$, the condition $a_{AB} L_Z < 1$ gives uniqueness and Ulam–Hyers stability with $C = a_{AB}/(1 - a_{AB}L_Z)$.

## Expansion

A $\zeta$-approximate solution satisfies ${}^{C}D^{\vartheta} V = Z(t,V) + \varpi(t)$ with $|\varpi| \le \zeta$, so $V = \mathcal T V + I^{\vartheta}\varpi$ and $|I^{\vartheta}\varpi(t)| \le \zeta t^{\vartheta}/\Gamma(\vartheta+1) \le a\zeta$, which is item 2. Item 1 is the bound $|I^{\vartheta}(Z(\cdot,P) - Z(\cdot,\bar P))| \le aL_Z\|P - \bar P\|$ and Banach's fixed point theorem. For item 3 take $\bar V$ the unique solution: $\|V - \bar V\| \le \|V - \mathcal TV\| + \|\mathcal TV - \mathcal T\bar V\| \le a\zeta + aL_Z\|V - \bar V\|$, and rearrange. In applications to vector-host or co-infection models the Lipschitz constant comes from bounds on the compartments in the invariant region (mass-action terms are Lipschitz on bounded sets), and the resulting condition restricts the time horizon $\tau$ rather than the epidemiological parameters; Ulam–Hyers stability says that numerical schemes with small residual stay close to the true trajectory, not that the epidemic tends to an equilibrium.

## Sources

- T.-Q. Tang, R. Jan, E. Bonyah, Z. Shah, E. Alzahrani, "Qualitative analysis of the transmission dynamics of dengue with the effect of memory, reinfection, and vaccination", Computational and Mathematical Methods in Medicine 2022 (2022) 7893570, Eqs. (17)–(22) and (31)–(37), Definitions 4–5, Lemma 2 and Theorem 5, <https://doi.org/10.1155/2022/7893570>, PMCID PMC9553356.
- A. Selvam, S. Sabarinathan, B. V. Senthil Kumar, H. Byeon, K. Guedri, S. M. Eldin, M. I. Khan, "Ulam–Hyers stability of tuberculosis and COVID-19 co-infection model under Atangana–Baleanu fractal-fractional operator", Scientific Reports 13 (2023) 9012, Definitions 1–3, Theorems 1–4, <https://doi.org/10.1038/s41598-023-35624-4>, PMCID PMC10237533.
