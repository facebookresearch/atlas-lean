# Observability–identifiability rank condition

**Model.** Consider

$$\dot x(t) = f\big(x(t), u(t), w(t), \theta\big), \qquad y(t) = h\big(x(t), u(t), \theta\big),$$

with states $x \in \mathbb R^{n_x}$, known analytic inputs $u$, unknown smooth inputs or time-varying parameters $w \in \mathbb R^{n_w}$, constant unknown parameters $\theta \in \mathbb R^{n_\theta}$ and outputs $y \in \mathbb R^m$, all functions analytic. Augment the state to $\tilde x = (x^\top, \theta^\top, w^\top)^\top$ of dimension $n_{\tilde x} = n_x + n_\theta + n_w$, with $\dot\theta = 0$; when $w$ is present, one either assumes its derivatives vanish beyond some order $s$ or augments further with $\dot w, \ddot w, \dots$

**Definitions.** A parameter $\theta_i$ is *structurally locally identifiable* if for almost every $\theta^*$ there is a neighbourhood $\mathcal N(\theta^*)$ with $\hat\theta \in \mathcal N(\theta^*)$ and $y(t, \hat\theta) = y(t, \theta^*)$ for all $t$ implying $\hat\theta_i = \theta_i^*$. A state $x_i(\tau)$ is *observable* if it can be locally distinguished from neighbouring values using $y$ and $u$ on a finite interval. The model has *full input–state–parameter observability* (FISPO) if every coordinate of $\tilde x(t_0)$ is locally determined by $y$ and $u$ on some $[t_0, t_f]$.

**Extended Lie derivatives.** With augmented dynamics $\tilde f$, set $L^0_{\tilde f} h = h$ and

$$L^i_{\tilde f} h(\tilde x, u) = \frac{\partial L^{i-1}_{\tilde f} h}{\partial \tilde x}\,\tilde f(\tilde x, u) + \sum_{j=0}^{i-1} \frac{\partial L^{i-1}_{\tilde f} h}{\partial u^{(j)}}\, u^{(j+1)}, \qquad i \ge 1 .$$

**Theorem (observability–identifiability condition).** Let

$$\mathcal{OI}(\tilde x, u) = \frac{\partial}{\partial \tilde x}\begin{pmatrix} L^0_{\tilde f}h \\ L^1_{\tilde f}h \\ \vdots \\ L^{n_{\tilde x}-1}_{\tilde f}h \end{pmatrix} \in \mathbb R^{m n_{\tilde x} \times n_{\tilde x}} .$$

If $\operatorname{rank}\mathcal{OI}(\tilde x_0, u) = n_{\tilde x}$ at a generic point $\tilde x_0$, the model is structurally locally observable and identifiable (FISPO). If the rank is smaller, the coordinates whose removal does not lower the rank (equivalently, whose columns lie in the span of the other columns) are unidentifiable parameters or unobservable states.

**Consequences for epidemic models.** A compartment such as the recovered class, which feeds back into no other equation and is not measured, never appears in the output's Lie derivatives and is unobservable. Treating a parameter as time-varying (moving it from $\theta$ into $w$) can break symmetries of the model: a Lie symmetry such as $\mu \mapsto \mu + \epsilon\rho$ that renders two constant parameters unidentifiable disappears when one of them varies in time, and the model can gain identifiability and observability.

## Expansion

The output and its time derivatives along any trajectory are $y^{(i)}(t) = L^i_{\tilde f}h(\tilde x(t), u(t))$. Knowing $y$ on an interval gives all these derivatives at $t_0$, so the map $\tilde x_0 \mapsto (L^0 h, \dots, L^{n_{\tilde x}-1}h)$ is known; full rank of its Jacobian at $\tilde x_0$ makes it locally injective by the inverse function theorem, which is local weak observability in the sense of Hermann and Krener applied to the augmented state. Derivatives beyond order $n_{\tilde x} - 1$ add no rank for generic analytic systems. Applying the test across 36 published COVID-19 compartmental models and all plausible output choices (255 model versions) shows that many commonly fitted models are not FISPO with case counts alone, and that adding outputs, fixing parameters from prior knowledge, or reparametrising restores observability.

## Sources

- G. Massonis, J. R. Banga, A. F. Villaverde, "Structural identifiability and observability of compartmental models of the COVID-19 pandemic", Annual Reviews in Control 51 (2021) 441–459, Section 2 (Definitions 1–4, augmented system Eqs. 3–5, Theorem 1) and Section 4 (results, symmetry breaking by time-varying parameters, remedies), <https://doi.org/10.1016/j.arcontrol.2020.12.001> (PMC7752088).
- R. Hermann, A. J. Krener, "Nonlinear controllability and observability", IEEE Transactions on Automatic Control 22 (1977) 728–740, <https://doi.org/10.1109/TAC.1977.1101601>.
