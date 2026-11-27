# Averaging bound for periodically switched transmission

**Model class.** Let the state $x(t) \in \mathbb{R}^n$ of a compartmental model satisfy the control-affine equation

$$\dot x = f_0(x) + \sum_{i=1}^{m} \beta_i(t)\, f_i(x),$$

with $f_0, \dots, f_m$ continuously differentiable and each modulation $\beta_i \in L^\infty(\mathbb{R}_{\ge 0}; [\beta_i^-, \beta_i^+])$ (for example $\beta_i = 1$ outside lockdown and $\beta_i < 1$ during lockdown). The SIR model is the case $n = 3$, $m = 1$, $x = (S, I, R)$,

$$f_0(x) = (0, -\alpha I, \alpha I), \qquad f_1(x) = \tfrac{1}{N}(-\sigma S I, \sigma S I, 0),$$

whose reproduction number under constant $\beta_1 = \beta$ is $\mathcal{R}_0 = \beta \sigma / \alpha$.

**Theorem (averaging estimate).** Let $K \subset \mathbb{R}^n$ be compact and positively invariant for every admissible choice of the $\beta_i$. There are strictly increasing functions $\alpha_1, \alpha_2, \alpha_3 : \mathbb{R}_{\ge 0} \to \mathbb{R}_{\ge 0}$ such that for all $x_0, x_0^\ast \in K$, all periods $T_i > 0$, all $T_i$-periodic $\beta_i$ and all constants $\beta_i^\ast \in [\beta_i^-, \beta_i^+]$, the solutions $x$ (with $\beta_i$, $x(0) = x_0$) and $x^\ast$ (with $\beta_i^\ast$, $x^\ast(0) = x_0^\ast$) satisfy

$$\sup_{0 \le s \le t} \|x(s) - x^\ast(s)\| \le \alpha_1(t)\, \mathrm{IC} + \alpha_2(t)\, \mathrm{P} + \alpha_3(t)\, \mathrm{A} \qquad (t \ge 0),$$

where $\mathrm{IC} = \|x_0 - x_0^\ast\|$, $\mathrm{P} = \max_i T_i$ and $\mathrm{A} = \max_i \bigl| \tfrac{1}{T_i} \int_0^{T_i} \beta_i(s)\, ds - \beta_i^\ast \bigr|$.

In particular, if each $\beta_i$ has mean $\beta_i^\ast$ and the initial states agree, the deviation on any bounded horizon is $O(\max_i T_i)$, and as the switching period tends to zero the switched epidemic converges uniformly on compact time intervals to the averaged system $\dot x^\ast = f_0(x^\ast) + \sum_i \beta_i^\ast f_i(x^\ast)$.

**Averaged reproduction number.** For a lockdown policy alternating $X$ open days with $Y$ lockdown days, with duty cycle $\mathrm{DC} = X/(X + Y)$, and a model whose reproduction number is affine in the modulations (as in SIR), the averaged system has

$$\mathcal{R}_0^\ast = \mathrm{DC}\, \mathcal{R}_0^+ + (1 - \mathrm{DC})\, \mathcal{R}_0^-,$$

the duty-cycle-weighted average of the open and lockdown reproduction numbers. Fast switching with $\mathcal{R}_0^\ast < 1$ therefore suppresses the epidemic even though $\mathcal{R}_0^+ > 1$ during open days.

## Expansion

The estimate is a quantitative first-order averaging result. Writing $\beta_i = \beta_i^\ast + (\bar\beta_i - \beta_i^\ast) + \tilde\beta_i$ with $\bar\beta_i$ the mean and $\tilde\beta_i$ zero-mean and $T_i$-periodic, the antiderivative of $\tilde\beta_i$ is bounded by a multiple of $T_i$; integrating by parts in the variation-of-constants difference of the two solutions turns the oscillating forcing into an $O(T_i)$ term, the mean offset contributes $O(\mathrm{A})$, and Grönwall's inequality on $K$ (where the $f_i$ and their derivatives are bounded) propagates both, giving the growth functions $\alpha_j(t)$. For the SIR model with constant $\beta$ and $\mathcal{R}_0 > 1$, an outbreak occurs iff $S(0) > N/\mathcal{R}_0$; with $R(0) = 0$ the peak prevalence is

$$I_p = N + \frac{N}{\mathcal{R}_0}\left(\log \frac{N}{\mathcal{R}_0\, S(0)} - 1\right),$$

from the conserved quantity $S + I - (N/\mathcal{R}_0)\log S$ evaluated at $S = N/\mathcal{R}_0$, which is why an early lockdown that keeps $I(0)$ small lowers and delays the peak once switching begins.

## Sources

- M. Bin, P. Y. K. Cheung, E. Crisostomi, P. Ferraro, H. Lhachemi, R. Murray-Smith, C. Myant, T. Parisini, R. Shorten, S. Stein, L. Stone, "Post-lockdown abatement of COVID-19 by fast periodic switching", PLoS Computational Biology 17 (2021) e1008604, section "Theoretical underpinnings of FPSP", Equations (1), (2), (11), (12), Theorem 1 and Comments A–B, <https://doi.org/10.1371/journal.pcbi.1008604> (PMC7861565).
