# Well-posedness and positivity of the reaction–diffusion SIR model with Lévy jumps

**Model.** On an open bounded domain $\mathcal{U} \subset \mathbb{R}^n$ with $C^2$ boundary, with homogeneous Neumann boundary conditions and nonnegative initial data, consider

$$
\begin{aligned}
dS &= \bigl[d_1\Delta S + \Lambda(x) - \mu(x) S - F(S, I)\bigr]dt + \int_{\mathbb{Z}} \mathcal{C}_1(z, x)\, S(t-, x)\,\tilde N(dt, dz),\\
dI &= \bigl[d_2\Delta I - (\mu(x) + \gamma(x)) I + F(S, I)\bigr]dt + \int_{\mathbb{Z}} \mathcal{C}_2(z, x)\, I(t-, x)\,\tilde N(dt, dz),\\
dR &= \bigl[d_3\Delta R - \mu(x) R + \gamma(x) I\bigr]dt + \int_{\mathbb{Z}} \mathcal{C}_3(z, x)\, R(t-, x)\,\tilde N(dt, dz),
\end{aligned}
$$

where $d_i > 0$, $\Lambda, \mu, \gamma$ are positive essentially bounded functions, $\tilde N$ is a compensated Poisson random measure with $\sigma$-finite intensity $\nu$, and the jump intensities $\mathcal{C}_i$ are essentially bounded. The incidence $F : [0,\infty)^2 \to [0,\infty)$ is either
- **(P1)** globally Lipschitz (e.g. standard incidence $\beta(x)\,si/(s+i)$), or
- **(P3)** locally Lipschitz with $F(s, i) \le C_F s$ (e.g. Crowley–Martin incidence $\beta(x)\,si/(1 + ai + bsi)$).

**Theorem.**
1. Under (P1), for every $u_0 = (S_0, I_0, R_0) \in L^2(\mathcal{U})^3$, and under (P3), for every $u_0 \in L^\infty(\mathcal{U})^3$, the system has a pathwise unique global càdlàg mild solution $u(t) = \mathcal{S}(t)u_0 + \int_0^t \mathcal{S}(t-s)\mathcal{F}(u(s))\,ds + \int_0^t\!\int_{\mathbb{Z}} \mathcal{S}(t-s)\mathcal{G}(z, u(s-))\,\tilde N(ds, dz)$, depending continuously on $u_0$; here $\mathcal{S}$ is the Neumann heat semigroup.
2. The mild solution is the mean-square limit, uniformly on $[0,T]$, of strong solutions of the problems regularized by the resolvent $\theta\mathcal{R}(\theta)$ of the diffusion operator, as $\theta \to \infty$.
3. For both incidence classes the mild solution stays almost surely nonnegative.

## Proof sketch

Writing the system as an abstract evolution equation $du = (\mathcal{A}u + \mathcal{F}(u))dt + \int \mathcal{G}(z, u)\,\tilde N$, existence follows from a Banach fixed-point argument in a space of adapted càdlàg processes with an exponentially weighted norm $e^{-\lambda t}$; choosing $\lambda$ large makes the map a contraction whatever the biological parameters. For the locally Lipschitz class, a truncation of $F$ plus the bound $F \le C_F s$ (which keeps $S$ bounded in $L^\infty$) removes the truncation. Positivity is proved on the regularized strong solutions by applying Itô's formula to a smooth convex penalty $\eta_\epsilon$ of the negative part, then passing to the limit $\theta \to \infty$, $\epsilon \to 0$.

## Related topics

- [Kermack–McKendrick SIR model](../../kermack-mckendrick-sir-model/README.md)

## Sources

- Mohamed Mehdaoui, "Well-posedness results for a new class of stochastic spatio-temporal SIR-type models driven by proportional pure-jump Lévy noise", *Applied Mathematical Modelling* 126 (2024), 543–567, <https://doi.org/10.1016/j.apm.2023.11.017>. Preprint version: arXiv:2303.18239 (2023), spatio-temporal SIR system with Neumann boundary conditions (Section 1), Definition 2.4, Theorems 3.1–3.3, Lemmas 4.1–4.3, Theorem 4.1, <https://doi.org/10.48550/arXiv.2303.18239>.
