# Sensitive-resistant model with drug-induced resistance

Let $S(t), R(t) \ge 0$ be the sensitive and resistant tumour fractions, nondimensionalized so that the carrying capacity is $1$ and the sensitive growth rate is $1$. Let $u : [0,\infty) \to [0, u_{\max}]$ be a bounded measurable drug dose. With spontaneous resistance rate $\epsilon > 0$, induction rate $\alpha \ge 0$, cytotoxicity $d \ge 0$ against sensitive cells and relative resistant growth rate $p_r > 0$, consider

$$
\begin{aligned}
\dot S &= \big(1 - (S + R)\big) S - \big(\epsilon + \alpha u(t)\big) S - d\, u(t)\, S,\\
\dot R &= p_r\big(1 - (S + R)\big) R + \big(\epsilon + \alpha u(t)\big) S .
\end{aligned}
$$

Resistance thus arises spontaneously at rate $\epsilon$ and is induced by the drug at rate $\alpha u(t)$; $\alpha = 0$ is the purely selective (Luria–Delbrück) case.

**Theorem (well-posedness and invariance).** For every such $u$ and initial condition in $\mathcal{T} = \{(S,R) : S, R \ge 0,\ S + R \le 1\}$, there is a unique solution defined for all $t \ge 0$, and $\mathcal{T}$ is forward invariant.

**Theorem (eventual resistance).** For every such $u$ and initial condition in $\mathcal{T} \setminus \{(0,0)\}$, $(S(t), R(t)) \to (0, 1)$ as $t \to \infty$. The origin $(0,0)$ is an equilibrium for every $u$.

**Identifiability.** If treatment starts from a purely sensitive tumour, $S(0) = S_0 \in (0, 1)$ and $R(0) = 0$, and $d > 0$ and $p_r < 1$ as in the source's model, then $V = S + R$ and its time derivatives at $t = 0$, observed under a small set of designed controls $u$ (the source's Eq. (A13)), determine all of $d$, $\epsilon$, $p_r$, and $\alpha$ (structural identifiability).

## Expansion

The axes behave well: $S = 0$ forces $\dot S = 0$, and $R = 0$ forces $\dot R \ge 0$, so solutions stay non-negative; the volume satisfies $\dot V = a(t)(1 - V) - b(t)$ with $a = S + p_r R \ge 0$ and $b = d u S \ge 0$, so $V \le 1$ is preserved, which with analyticity of the vector field gives global existence. In $\mathcal{T}$, $\dot R \ge 0$, so $R(t)$ increases to a limit $R^{*}$. If $\liminf S = \rho > 0$, then $\dot R \ge \epsilon \rho / 2$ eventually, contradicting boundedness, so $\rho = 0$. If $\liminf (S + R) < 1$, then $\dot R \ge p_r \bar\epsilon R$ eventually for some $\bar\epsilon > 0$, again contradicting boundedness (note $R$ becomes positive because $\epsilon > 0$). Hence $R^{*} = 1$, after which $\dot S < 0$ and $S \to 0$. Since all tumours become resistant, therapy can only delay progression; the induction rate shapes how long, and it reverses the ranking of schedules: constant infusion beats pulsed dosing when the drug only selects, while pulsed therapy wins when the drug also induces resistance.

## Sources

- J. M. Greene, J. L. Gevertz, E. D. Sontag, "Mathematical approach to differentiate spontaneous and induced evolution to drug resistance during cancer treatment", JCO Clinical Cancer Informatics 3 (2019) 1–20, Eqs. (1)–(5), Appendix Eqs. (A1)–(A3), Theorems 1–2, and the structural identifiability appendix (Eqs. (A13)–(A17)), <https://doi.org/10.1200/cci.18.00087>, PMCID PMC6873992.
