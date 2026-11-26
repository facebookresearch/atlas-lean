# Forced-wave selection at the borderline shift speed

**Model.** A population $n(t,x)$ on $\mathbb{R}$ follows $n_t - n_{xx} = n\big(\mathbf{g}(x - s(t)) - n\big)$ with climate shift $s(t) = 2t - \tfrac32\ln(1+t)$ and initial data $n_0 \in L^\infty(\mathbb{R};[0,1])$, $\liminf_{x\to-\infty} n_0 > 0$, $n_0 = 0$ for $x \ge x_0$. The profile $\mathbf{g} \in L^\infty$ is increasing with $\mathbf{g}(-\infty) = 1-a$, $\mathbf{g}(+\infty) = 1$ for some $a \in (0,1)$, and $|\mathbf{g}(y) - (1-a)| \in L^1((-\infty,0))$, $y|1 - \mathbf{g}(y)| \in L^1((0,\infty))$.

**Theorem.** For every $A > 0$ there is a unique positive bounded solution $U_A$ of the forced-wave equation
$$ U_A'' + 2U_A' + U_A(\mathbf{g} - U_A) = 0 \ \text{ in } \mathbb{R}, \qquad U_A(-\infty) = 1 - a,\quad U_A(+\infty) = 0,\quad \lim_{\xi\to+\infty}\frac{U_A(\xi)}{\xi e^{-\xi}} = A . $$
The solution $n$ locks onto the moving interface and selects one member of this family: there is $A_\infty \in (0,\infty)$ with
$$ \lim_{t\to\infty}\sup_{|x|\le R}\big|n(t, s(t) + x) - U_{A_\infty}(x)\big| = 0 \qquad \text{for every } R > 0, $$
and the selected amplitude is
$$ A_\infty = \frac{1}{2\sqrt\pi}\lim_{t\to\infty}(1+t)^{-3/2}\int_{\mathbb{R}}\mathfrak{m}(x)e^{x}n(t,s(t)+x)\,dx, $$
where $\mathfrak{m}$ is the unique positive solution of $\mathfrak{m}'' = (1 - \mathbf{g})\mathfrak{m}$, $\mathfrak{m}(-\infty) = 0$, $\mathfrak{m}'(+\infty) = 1$.

This regime separates nonlocal pulling ($\eta < 3/2$, decay rate $1 - \sqrt a$) from classical Fisher–KPP propagation ($\eta > 3/2$, decay rate $1$) for shifts $s(t) = 2t - \eta\ln(1+t)$: the speed stays $2$ while the selected decay rate jumps.

## Depends on

- [Logarithmic front corrections for Fisher–KPP in a shifting environment](logarithmic-front-corrections-for-fisher-kpp-in-a-shifting-environment.md)

## Expansion

At $\eta = \tfrac32$ the environmental lag $\tfrac32\ln t$ matches the Bramson lag of a speed-2 front exactly, so the front neither escapes ahead of the interface nor falls behind it. In the moving frame, $e^{x}n$ approximately solves a heat equation with potential $1 - \mathbf{g}$, whose large-time profile is $(4\pi)^{-1/2}t^{-3/2}\mathfrak{m}(x)$ times a weighted mass. That weighted mass converges, fixing the coefficient $A$ of the $\xi e^{-\xi}$ tail, which picks out $U_{A_\infty}$ from the one-parameter family of forced waves.

## Sources

- Émeric Bouin, King-Yeung Lam and Chang-Hong Wu, "Logarithmic corrections and interacting fronts in shifting environments and competition systems", arXiv:2610.26702 (2026), Section 1, Theorem 1.3; Section 6 (selection of a forced wave), <https://doi.org/10.48550/arXiv.2610.26702>.
