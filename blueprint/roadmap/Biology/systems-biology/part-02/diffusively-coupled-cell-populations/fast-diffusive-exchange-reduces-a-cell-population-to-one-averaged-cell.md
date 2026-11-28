# Fast diffusive exchange reduces a coupled cell population to one averaged cell

Let $N$ identical cells of volume $V_c$ share an extracellular medium of volume $N V_c$. Intracellular concentrations $\xi^{(i)} \in \mathbb{R}^n_+$ follow $\dot\xi^{(i)} = F(\xi^{(i)})$ with $F$ continuously differentiable, molecules cross the membrane with flux proportional to the concentration difference (diffusion rate $k_{\mathrm{diff}} \ge 0$), and the medium concentration $\xi^{(0)}$ decays at rate $k_d \ge 0$:

$$
\begin{aligned}
\dot\xi^{(0)} &= -k_d\, \xi^{(0)} + \sum_{j=1}^N \frac{k_{\mathrm{diff}}}{N V_c}\big(\xi^{(j)} - \xi^{(0)}\big),\\
\dot\xi^{(i)} &= F(\xi^{(i)}) - \frac{k_{\mathrm{diff}}}{V_c}\big(\xi^{(i)} - \xi^{(0)}\big), \qquad i = 1, \dots, N.
\end{aligned}
$$

With $\varepsilon = k_{\mathrm{diff}}^{-1}$ and the slow variable $x = \xi^{(0)} + \frac1N\sum_j \xi^{(j)}$, the quasi-steady-state equations $z^{(i)} - x + \frac1N\sum_j z^{(j)} = 0$ have the unique solution $z^{(i)} = x/2$ for all $i$ (the matrix $\frac1N\mathbf{1}\mathbf{1}^\top + I$ has eigenvalue $2$ once and $1$ with multiplicity $N-1$). The **slow model** is

$$
\dot x = F\!\left(\tfrac{x}{2}\right) - k_d\, \tfrac{x}{2},
$$

and the **boundary-layer model** $\frac{dy^{(i)}}{d\tau} = -\frac{1}{V_c}\big(y^{(i)} + \frac1N\sum_j y^{(j)}\big)$ for $y^{(i)} = z^{(i)} - x/2$ is linear with eigenvalues $-2/V_c$ ($n$ times) and $-1/V_c$ ($n(N-1)$ times).

**Proposition.** Let $\bar x$ be an equilibrium of the slow model, $F(\bar x/2) = k_d \bar x/2$. Suppose $F$ is globally Lipschitz on $\mathbb{R}^n_+$ and there is a quadratic Lyapunov function $V_S$ for the slow model about $\bar x$ (with $d_1\|x - \bar x\|^2 \le V_S \le d_2\|x-\bar x\|^2$, $\dot V_S \le -c_2\|x - \bar x\|^2$ on a sublevel set $\{d_1\|x-\bar x\|^2 \le D\}$, and $\|\partial V_S/\partial x\| \le c\,\|x - \bar x\|$). Then for initial data with $d_2\|x_0 - \bar x\|^2 \le \varrho D$, $0 \le \varrho < 1$, there is $\varepsilon^* > 0$ such that whenever $k_{\mathrm{diff}} > 1/\varepsilon^*$ the deviations $w(t) = (\xi^{(i)}(t) - \bar x/2)_{i=0,\dots,N}$ satisfy

$$
\|w(t)\| \le \beta(\|w(0)\|, t) + \mu(\varepsilon), \qquad \mu(\varepsilon) \to 0 \text{ as } \varepsilon \to 0,
$$

with $\beta$ of class $\mathcal{KL}$. Every cell and the medium thus converge to within $\mu(\varepsilon)$ of the common value $\bar x/2$: the population behaves as a single cell running the slow model.

For a bistable autoactivating switch $F(\xi) = 3\xi^2/(1+\xi^2) - \xi$ with $k_d = 0$, the result predicts synchronization of all switches and population-level bistability for fast exchange; simulations show that for slower exchange individual cells can settle on different stable states.

## Expansion

In the coordinates $(x, z^{(1)}, \dots, z^{(N)})$ the model has the standard singularly perturbed form $\dot x = f(x,z)$, $\varepsilon\dot z = g(x,z,\varepsilon)$. The quasi-steady map $h(x) = (x/2, \dots, x/2)$ has $\|\partial h/\partial x\| = \sqrt{N}/2$; the slow-model Lyapunov condition is a hypothesis; the linear boundary-layer model is Hurwitz by the eigenvalue computation and independent of $x$, so $V_B$ can be chosen with $\partial V_B/\partial x = 0$; and global Lipschitz continuity of $F$ together with the gradient bound on $V_S$ supplies the interconnection estimates. The general practical-stability theorem for singularly perturbed systems then gives the bound.

## Proof depends on

- [Practical stability of singularly perturbed systems from slow and boundary-layer Lyapunov functions](practical-stability-of-singularly-perturbed-systems-with-lyapunov-bounds.md)

## Sources

- S. Waldherr and F. Allgöwer, *Network-level dynamics of diffusively coupled cells*, arXiv:1212.4270 (2012), Section 3 (population model, Lemma 2, Proposition 1) and Section 4 (coupled switches). <https://doi.org/10.48550/arXiv.1212.4270>
