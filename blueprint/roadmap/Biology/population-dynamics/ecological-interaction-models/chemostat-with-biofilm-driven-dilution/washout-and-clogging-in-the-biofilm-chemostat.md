# Washout and clogging in a chemostat with biofilm-driven dilution

**Model.** In a chemostat whose wall biofilm $w$ occupies volume, the fluid volume shrinks and the dilution rate becomes $D(w) = D_0 w_0/(w_0 - w)$, with $w_0$ the biofilm capacity, so $D(w) \to \infty$ as $w \uparrow w_0$. In dimensionless form, with nutrient $S$, planktonic biomass $u$, wall biomass $w$, uptake functions $f, g$ ($C^1$, increasing, $f(0) = g(0) = 0$; Monod $g(S) = m_2 S/(a_2 + S)$ in the examples), adhesion rate $\alpha$ and sloughing rate $\beta$, the model is $\dot S = D(w)(1-S) - f(S)u - g(S)w$, $\dot u = (f(S) - D(w))u - \alpha u + \beta w$, $\dot w = (g(S) - \beta)w + \alpha u$ with $D(w) = w_0/(w_0 - w)$. Multiplying the vector field by $(1 - w/w_0)$ gives the **rescaled system**

$$\dot S = 1 - S - \Big(1 - \tfrac{w}{w_0}\Big)[u f(S) + w g(S)],\quad \dot u = -u + \Big(1 - \tfrac{w}{w_0}\Big)[(f(S) - \alpha)u + \beta w],\quad \dot w = \Big(1 - \tfrac{w}{w_0}\Big)[\alpha u + (g(S) - \beta)w]$$

on $\Omega = \{0 \le S \le 1,\ u \ge 0,\ 0 \le w \le w_0\}$, which is well posed (Theorem 2.1), has the same orbits and equilibria in $\{w < w_0\}$, and has exactly two boundary equilibria: washout $E_0 = (1,0,0)$ and the **clogged state** $E_w = (1,0,w_0)$. Let $A = f(1) - 1 - \alpha$, $B = g(1) - \beta$.

**Theorem 3.1.** $E_0$ is locally exponentially stable if and only if $A < 0$, $B < 0$ and $AB > \alpha\beta$.

**Theorem 3.2.** If $E_0$ is locally exponentially stable, it attracts every solution of the rescaled system starting in the interior of $\Omega$.

**Clogged state.** $E_w$ is locally exponentially stable if $\beta < g(1)$ and a saddle with stable manifold $\{w = w_0\}$ if $\beta > g(1)$.

- **Lemma 4.1.** If $E_w$ is locally exponentially stable, then $E_0$ is unstable.
- **Lemma 4.2.** If a solution of the original system reaches the clogged state, it does so in finite time.
- **Theorem 4.3.** If $f(1) - \alpha < 1$ and $\beta > 0$ is sufficiently small, then $E_w$ attracts all interior solutions of the rescaled system.

Thus washout is decided by the $2\times2$ linearization $M = \begin{pmatrix} A & \beta \\ \alpha & B\end{pmatrix}$ of the planktonic-wall exchange, while weak sloughing ($\beta < g(1)$) lets the biofilm grow to capacity, where the dilution rate blows up and the reactor clogs in finite time.

## Depends on

- [Chemostat equilibria and the washout threshold](../../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

At $E_0$ the Jacobian is block triangular with eigenvalue $-1$ and the eigenvalues of the cooperative matrix $M$, whose principal eigenvalue $\lambda_2$ has a positive left eigenvector $(U, W)$. Because $f(S) \le f(1)$, $g(S) \le g(1)$ and $D(w) \ge 1$, the function $L = Uu + Ww$ satisfies $\dot L \le \lambda_2(1 - w/w_0)L$; with $\lambda_2 < 0$, LaSalle's principle and the saddle structure of $E_w$ (when $B < 0$) force convergence to $E_0$. At $E_w$ the normal eigenvalue is $-(g(1) - \beta)$. Near a stable $E_w$, $(w_0 - w)/w_0$ decays like $e^{-\nu\tau}$ with $\nu = g(1) - \beta$ in rescaled time, and since $dt/d\tau = (w_0 - w)/w_0$ is integrable, the original time to clog is finite. Global attraction for small $\beta$ uses the increasing auxiliary function $G(b) = g^{-1}(b) + b w_0 f(g^{-1}(b))/(4(1 + \alpha - f(1))) + b w_0/4$ and its root $b^*$ of $G(b^*) = 1$: for $\beta < b^*$, the nutrient eventually stays where wall growth outpaces sloughing.

## Sources

- Xiaochen Duan and Sergei S. Pilyugin, "A Chemostat Model with Variable Dilution Rate Due to Biofilm Growth", SIAM Journal on Applied Mathematics 85 (2025), 2295–2317, <https://doi.org/10.1137/24m1704890>; numbering as in arXiv:2411.05213: Theorems 2.1, 3.1, 3.2, 4.3, 5.6, 5.9, 6.1, 6.2, 6.3 and Lemmas 4.1, 4.2.
