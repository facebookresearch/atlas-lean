# Jacobi flows from ratios of squared Bessel flows and the primitive Eve process

**Jacobi processes and flows.** For $\delta, \delta' \in \mathbb{R}$, a $\mathrm{Jacobi}(\delta,\delta')$ process solves

$$dY_t = 2\sqrt{Y_t(1-Y_t)}\,d\gamma_t + \big(\delta(1-Y_t) - \delta' Y_t\big)\,dt$$

on $[0,1]$; in population genetics it is the Wright–Fisher diffusion with (possibly negative) mutation rates $(\delta, \delta')$, with $\delta = \delta' = 0$ dual to Kingman's coalescent. A $\mathrm{Jacobi}(\delta,\delta')$ *flow* is a family $(\mathcal{Y}_{s,t}(v))_{t\ge s,\,v\in[0,1]}$ of such processes, one for each initial time $s$ and initial frequency $v$, all driven by a single white noise $\mathcal{W}$ on $[0,1] \times \mathbb{R}$ through the martingale measure $\mathcal{M}(A \times [s,t]) = \mathcal{W}(A \times [s,t]) - \lambda(A \cap [0,1])\,\mathcal{W}([0,1] \times [s,t])$:

$$\mathcal{Y}_{s,t}(v) = v + 2\int_s^t \mathcal{M}\big([0,\mathcal{Y}_{s,r}(v)], dr\big) + \int_s^t\big(\delta(1-\mathcal{Y}_{s,r}(v)) - \delta'\mathcal{Y}_{s,r}(v)\big)\,dr,$$

with absorption at the boundary; it is the flow of bridges (in the sense of Bertoin and Le Gall) describing a Fleming–Viot population with mutation, the point $v$ tracking the mass of the descendants of the initial interval $[0,v]$.

**Theorem (disintegration: Jacobi flows inside squared Bessel flows).** Let $\mathcal{S}$ be a $\mathrm{BESQ}^\delta$ flow driven by a white noise $\mathcal{W}$, and let $f$ solve $f(x) = b + 2\int_0^x \mathcal{W}([0,f(s)],ds) + (\delta+\delta')x$ (a $\mathrm{BESQ}^{\delta+\delta'}$ total mass started at $b > 0$, absorbed at $0$ at time $\mathfrak{d}_f$). The $\mathrm{BESQ}^{\delta,\delta'}_b$ flow $\Theta$ consists of the flow lines $\mathcal{S}_{r,\cdot}(a)$, $a \in [0,f(r)]$, each followed until it meets $f$ and equal to $f$ afterwards. After normalizing by $f$ and the time change $\eta_f(x) = \int_0^x dr/f(r)$, the resulting flow $\mathcal{Y}^+$ is a $\mathrm{Jacobi}(\delta,\delta')$ flow on the positive time axis, the pathwise unique strong solution of the flow SDE above, and it is independent of $f$. This is a flow version of Perkins' disintegration of a Feller continuous-state branching population into total mass and a Fleming–Viot process of type frequencies.

**Theorem (pathwise construction).** All $\mathrm{Jacobi}(\delta,\delta')$ flows, simultaneously for all real $\delta, \delta'$, can be built from a single one-dimensional two-sided Brownian motion $(B_t)_{t\in\mathbb{R}}$, with local time $\mathfrak{L}_t$ at $0$ (taken negative for $t<0$). This is done through the two-sided perturbed reflecting Brownian motions ($\mu$-processes) $X^\mu_t = |B_t| - \mu\mathfrak{L}_t$, $t\in\mathbb{R}$, one for each $\mu>0$, all built from that Brownian motion: the local times of $X^\mu$ form a $\mathrm{BESQ}^{2/\mu}$ flow forward and a killed $\mathrm{BESQ}^{2-2/\mu}$ flow backward, and the space-time transformation above turns these BESQ flows into Jacobi flows.

**Proposition (primitive Eve).** Fix $\mu>0$ and let $Y$ be the flow built from a two-sided perturbed reflecting Brownian motion with parameter $\mu$ (the flow of Remark 4.8 of the source): its forward flow on the positive time axis is a $\mathrm{Jacobi}(\delta,0)$ flow with $\delta=2/\mu$, and its backward flow on the negative time axis is a killed $\mathrm{Jacobi}(2-\delta,0)$ flow (so here $\delta'=0$). Let $\Xi_r = \inf\{v \in [0,1] : Y_{r,x}(v) = 1 \text{ for some } x < r\}$, the "primitive Eve" process (the location of the ancestor of the whole population). Then $\Xi_0 \sim \mathrm{Beta}(\delta/2, 1)$, and conditionally on $\Xi_0$, $(\Xi_{-t})_{t\ge0}$ and $(\Xi_t)_{t\ge0}$ are independent $\mathrm{Jacobi}(\delta,2)$ and $\mathrm{Jacobi}(\delta,0)$ processes.

## Expansion

Ratios of independent squared Bessel (Gamma-type) processes are Jacobi processes after a time change, which is the one-dimensional version of the disintegration; the flow version keeps track of all initial levels at once using one driving noise; the martingale measure driving the normalized flow turns out to be independent of $f$. In the perturbed reflecting Brownian motion picture, levels of local time play the role of population sizes indexed by space, so Ray–Knight theorems produce BESQ flows; the dual relation between BESQ$^\delta$ and BESQ$^{2-\delta}$ flows matches forward and backward Jacobi flows. The Eve process is read off from where the excursions that eventually cover the whole population started.

## Sources

- Elie Aïdékon, Yueyun Hu and Zhan Shi, "The stochastic Jacobi flow", Ann. Probab. 54 (2026), 1126–1163, <https://doi.org/10.1214/24-AOP1737>. Numbering follows the arXiv version, arXiv:2306.12716 (2023): Definitions of BESQ$^{\delta,\delta'}_b$ and Jacobi flows (Section 4), Propositions 2.4 and 2.7, Theorem 4.6, Corollary 4.7, Theorem 5.3 and Proposition 5.10, <https://doi.org/10.48550/arXiv.2306.12716>.
