# Tumor–estrogen–fat model of ER-positive breast cancer

Let $T(t)$ be tumor volume, $E(t)$ the intratumoral estrogen concentration and $F(t)$ the volume of adjacent fat at time $t$ (days). Fat is the estrogen source, tumor growth is estrogen driven with Michaelis–Menten saturation, and tumor cells consume fat:

$$\frac{dT}{dt} = \frac{k_1E}{a_1 + E}\,T\,(1 - m_1T), \qquad \frac{dE}{dt} = rF - \mu E, \qquad \frac{dF}{dt} = -\alpha TF,$$

with positive parameters $k_1$ (maximal growth rate), $a_1$ (half-saturation estrogen level), $m_1$ (inverse carrying capacity), $r$ (estrogen production by fat), $\mu$ (washout) and $\alpha$ (fat consumption), and non-negative initial data $(T_0,E_0,F_0)$. Diet enters only through $F_0$ (high-fat versus control diet).

**Proposition 1.** For non-negative initial conditions the system has a unique solution, which is non-negative and bounded for all $t \ge 0$. Moreover, for all $t \ge 0$,

$$F(t) \le F_0, \qquad T(t) \le \max\Big\{T_0, \frac{1}{m_1}\Big\}, \qquad \limsup_{t\to\infty} E(t) \le \frac{rF_0}{\mu}.$$

The source's proof of Proposition 1 prints the inequality $T' \le k_1T(1 - m_1T)$ ((2.5)) and the conclusion $\limsup_{t\to\infty} m_1T \le 1/m_1$ ((2.6)), and is read as giving $\limsup_{t\to\infty} T \le 1/m_1$; this page states the bound $T \le \max\{T_0, 1/m_1\}$ instead, because (2.5) is false for $T > 1/m_1$ and $\limsup T \le 1/m_1$ fails whenever $T_0 > 1/m_1$ (with $k_1 = a_1 = m_1 = r = \mu = \alpha = 1$ and $(T_0, E_0, F_0) = (2, 0, 1)$, $T(t) \to 1.46$).

## Expansion

The right-hand side is locally Lipschitz, giving local existence and uniqueness. Non-negativity follows coordinate by coordinate: $F(t) = F_0\exp(-\alpha\int_0^tT)$, then $E' \ge -\mu E$, then $T(t) = T_0\exp\big(\int_0^t g(E)(1 - m_1T)\big)$ with $g(E) = k_1E/(a_1+E)$. For the bounds, $g(E) \ge 0$ makes $T' \le 0$ whenever $T \ge 1/m_1$, so $T$ never exceeds $\max\{T_0, 1/m_1\}$; if $T_0 > 1/m_1$, $T$ stays above $1/m_1$, $F$ decays exponentially, $\int_0^\infty E < \infty$ and $T$ converges to a limit above $1/m_1$; $F' \le 0$ gives $F \le F_0$ and hence $E' \le rF_0 - \mu E$. Calibrated to mouse data with fat grafts, the model attributes the faster growth under a high-fat diet to a larger initial fat volume, which raises the estrogen supply.

## Sources

- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler, Vessela N. Kristensen, Arnoldo Frigessi, Alvaro Köhn-Luque, "Modeling of Mouse Experiments Suggests that Optimal Anti-Hormonal Treatment for Breast Cancer is Diet-Dependent", Bulletin of Mathematical Biology 86 (2024), 42, <https://doi.org/10.1007/s11538-023-01253-1>. Published version of arXiv:2301.10553, cited next; locators there refer to the arXiv version.
- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler and Vessela N. Kristensen, *Modeling of mouse experiments suggests that optimal anti-hormonal treatment for breast cancer is diet-dependent*, arXiv:2301.10553 (2023). <https://doi.org/10.48550/arXiv.2301.10553> Section 2.2 (model) and Section 2.3 (Proposition 1).
