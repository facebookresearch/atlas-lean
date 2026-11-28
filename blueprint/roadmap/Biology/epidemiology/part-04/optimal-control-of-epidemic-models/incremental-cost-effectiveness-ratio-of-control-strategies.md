# Cost-effectiveness ratios of control strategies

**Setting.** A finite set of control strategies $s = 1, \dots, K$ (single controls or combinations of controls in an optimally controlled epidemic model) is compared over a common horizon $[0, t_f]$ with the baseline $s = 0$ of no intervention, which has effect $E_0 = 0$ and cost $C_0 = 0$. Each strategy has a total cost $C_s \ge 0$, typically $C_s = \int_0^{t_f} \sum_k \tfrac{b_k}{2}\, u_k^{(s)}(t)^2\, dt$ for the controls it uses, and a total health effect $E_s$ relative to the baseline, measured in one fixed unit throughout the comparison, either

- **infections averted**, the difference in cumulative incident cases, $E_s = \int_0^{t_f} \big( \iota^{\mathrm{none}}(t) - \iota^{(s)}(t) \big)\, dt$ for the incidence rates $\iota$; or
- **infectious person-time averted**, $E_s = \int_0^{t_f} \big( I^{\mathrm{none}}(t) - I^{(s)}(t) \big)\, dt$ for the infectious stock $I$ (person-days, not cases).

**Ratios.** For a strategy with $E_s > 0$ the **average cost-effectiveness ratio** is $\mathrm{ACER}_s = C_s / E_s$, its cost per unit of effect against the baseline. For two strategies with $E_s > E_{s'}$ the **incremental cost-effectiveness ratio** is

$$\mathrm{ICER}(s \mid s') = \frac{C_s - C_{s'}}{E_s - E_{s'}},$$

the extra cost per extra unit of effect, so $\mathrm{ICER}(s \mid 0) = \mathrm{ACER}_s$. Some studies also report the infection averted ratio, $E_s$ divided by the number recovered under $s$.

**Frontier.** Start from the baseline and all strategies, ordered by increasing effect, and repeat until no strategy is removed:

1. *(Equal effect.)* Among strategies with equal effect, keep one of least cost.
2. *(Dominance.)* Remove any strategy $s'$ for which another remaining strategy $s$ has $E_s \ge E_{s'}$ and $C_s \le C_{s'}$, with one inequality strict.
3. *(Extended dominance.)* For consecutive remaining strategies $s_{i-1}, s_i, s_{i+1}$, remove $s_i$ if $\mathrm{ICER}(s_i \mid s_{i-1}) > \mathrm{ICER}(s_{i+1} \mid s_i)$.

The remaining strategies, the **cost-effectiveness frontier**, have positive and nondecreasing successive ICERs; they increase strictly once interior points collinear with their neighbours, where two successive ICERs are equal, are also removed.

**Decision at a willingness to pay.** For a willingness to pay $w \ge 0$ per unit of effect, the **net benefit** of strategy $s$ is $w E_s - C_s$, and the preferred strategies are those of largest net benefit among all strategies, the baseline included. A frontier with successive ICERs $\rho_1 \le \rho_2 \le \cdots$ from the baseline contains a preferred strategy: the last frontier strategy whose ICER is at most $w$, or the baseline if $\rho_1 > w$. Without a threshold $w$ the frontier ranks no single strategy first.

## Expansion

Plot each strategy as the point $(E_s, C_s)$. Dominance removes points lying above and to the left of another point; extended dominance removes points lying above the segment joining their neighbours, since a mixture of the neighbours achieves the same effect at lower cost. The frontier is the lower convex hull of the points from the baseline onward, and its segment slopes are the successive ICERs, which is why they are nondecreasing. The net benefit $wE - C$ is a linear function maximized over the hull at the vertex where the slope passes $w$, which gives the decision rule; for instance, from the baseline through $(1, 1)$ to $(2, 3)$ the ICERs are $1$ and $2$, and at $w = 3$ the second strategy, not the first, is preferred. ACER compares each strategy only with doing nothing, so ranking by ACER can disagree with the frontier. ICER values depend on the units of cost and effect, on the horizon and on whether the controls are optimized jointly or separately; in epidemic optimal-control studies the effects and costs are computed by solving the [optimality system](pontryagin-optimality-system-with-quadratic-control-costs.md) once per strategy, with the inactive controls fixed at zero. Applications include COVID-19 models with preventive and case-management controls and with an environmental compartment, a COVID-19–dengue co-infection model and a malaria–visceral-leishmaniasis co-infection model.

## Sources

- M. F. Drummond, M. J. Sculpher, K. Claxton, G. L. Stoddart, G. W. Torrance, *Methods for the Economic Evaluation of Health Care Programmes*, 4th ed., Oxford University Press (2015).
- M. C. Weinstein, W. B. Stason, "Foundations of cost-effectiveness analysis for health and medical practices", New England Journal of Medicine 296 (1977) 716–721, <https://doi.org/10.1056/NEJM197703312961304>.
- S. Olaniyi, O. S. Obabiyi, K. O. Okosun, A. T. Oladipo, S. O. Adewale, "Mathematical modelling and optimal cost-effective control of COVID-19 transmission dynamics", The European Physical Journal Plus 135 (2020) 938, Eq. (12), Tables 3–4, <https://doi.org/10.1140/epjp/s13360-020-00954-z> (PMC7688301).
- A. Omame, H. Rwezaura, M. L. Diagne, S. C. Inyama, J. M. Tchuenche, "COVID-19 and dengue co-infection in Brazil: optimal control and cost-effectiveness analysis", The European Physical Journal Plus 136 (2021) 1090, Section 6, <https://doi.org/10.1140/epjp/s13360-021-02030-6>.
- F. B. Agusto, I. M. ELmojtaba, "Optimal control and cost-effective analysis of malaria/visceral leishmaniasis co-infection", PLoS ONE 12 (2017) e0171102, Section 6 (Eqs. (13)–(14), Tables 5–8), <https://doi.org/10.1371/journal.pone.0171102> (PMC5293207).
- J. K. K. Asamoah, M. A. Owusu, Z. Jin, F. T. Oduro, A. Abidemi, E. O. Gyasi, "Global stability and cost-effectiveness analysis of COVID-19 considering the impact of the environment: using data from Ghana", Chaos, Solitons & Fractals 140 (2020) 110103, Section 4.2 (Eq. (21), Table 4), <https://doi.org/10.1016/j.chaos.2020.110103> (PMC7351453).
