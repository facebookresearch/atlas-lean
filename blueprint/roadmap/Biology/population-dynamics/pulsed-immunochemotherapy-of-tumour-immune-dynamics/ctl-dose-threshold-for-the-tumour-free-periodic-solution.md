# CTL dose threshold for the tumour-free periodic solution under pulsed immunotherapy

**Model.** Let $x(t)$ be the concentration of cytotoxic T lymphocytes (CTLs) at the tumour site and $y(t)$ the number of tumour cells. Between treatments ($t \ne n\tau$),

$$\dot x = s + \frac{\rho x y}{\alpha + y} - c_1 x y - d_1 x, \qquad \dot y = r y(1 - b y) - c_2 x y,$$

and at the treatment times $t = n\tau$, $n \in \mathbb{N}$, a dose $\mu_1 > 0$ of CTLs is infused: $x(n\tau^+) = x(n\tau) + \mu_1$, $y(n\tau^+) = y(n\tau)$. All parameters are positive.

**Lemma 1.** The tumour-free subsystem $\dot x = s - d_1 x$, $x(n\tau^+) = x(n\tau) + \mu_1$ has the globally attracting positive $\tau$-periodic solution

$$x^*(t) = \frac{s}{d_1} + \left(x^*(0^+) - \frac{s}{d_1}\right)e^{-d_1(t - n\tau)}, \quad t \in (n\tau, (n+1)\tau], \qquad x^*(0^+) = \frac{s}{d_1} + \frac{\mu_1}{1 - e^{-d_1\tau}},$$

so the full system has the tumour-free periodic solution $(x^*(t), 0)$.

**Theorem 2.** The tumour-free periodic solution $(x^*(t), 0)$ is locally asymptotically stable if

$$\mu_1 > \mu_1^c := \frac{(r d_1 - c_2 s)\,\tau}{c_2},$$

and unstable if $\mu_1 < \mu_1^c$ (Remark 3). At $\mu_1 = \mu_1^c$ a supercritical bifurcation produces a stable positive periodic solution (Theorem 4).

## Expansion

Linearising at $(x^*(t), 0)$ gives a triangular system whose tumour component obeys $\dot v_2 = (r - c_2 x^*(t)) v_2$, and the impulses act as the identity on the perturbation. The monodromy matrix over one period therefore has eigenvalues $e^{-d_1\tau} < 1$ and $e^{G}$ with

$$G = \int_0^\tau \big(r - c_2 x^*(t)\big)\,dt = r\tau - \frac{c_2 s\tau}{d_1} - \frac{c_2\mu_1}{d_1},$$

using $\int_0^\tau x^*(t)\,dt = (s\tau + \mu_1)/d_1$ (each pulse of size $\mu_1$ decays at rate $d_1$). By Floquet theory for impulsive systems the orbit is stable exactly when $G < 0$, which is the threshold condition. The threshold is the dose at which the period-averaged CTL level $(s\tau + \mu_1)/(d_1\tau)$ equals $r/c_2$, the CTL level at which killing balances the tumour's maximal per-capita growth rate; when $c_2 s > r d_1$ the natural CTL supply alone clears the tumour and $\mu_1^c < 0$.

## Sources

- L. Pang, L. Shen, Z. Zhao, "Mathematical Modelling and Analysis of the Tumor Treatment Regimens with Pulsed Immunotherapy and Chemotherapy", Computational and Mathematical Methods in Medicine (2016) 6260474, Section 2.1, Eqs. (1)–(15), Lemma 1, Theorems 2 and 4 and Remark 3, <https://doi.org/10.1155/2016/6260474>, PMCID PMC4779848.
