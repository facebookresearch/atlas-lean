# Linear determinacy of spreading speeds in cooperative reaction–diffusion systems

Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be smooth with $f(0) = 0$ and $f(\beta) = 0$ for some $\beta \gg 0$, with no equilibrium $\nu \gg 0$ strictly between $0$ and $\beta$, and suppose $f$ is cooperative (nonnegative off-diagonal partial derivatives) on $\mathcal{V}_\beta = \{p : 0 \le p \le \beta\}$. Let $D$ be a positive diagonal matrix and consider $\dot p = f(p) + D p_{xx}$ on $\mathbb{R}$. For solutions with initial data $p(0,\cdot)$ with values in $\mathcal{V}_\beta$, compact support, and strictly positive on a sufficiently long interval, the **slowest spreading speed** $c^*$ is characterized by: for every $\varepsilon > 0$,

$$\lim_{t\to\infty}\ \sup_{|x| \le (c^*-\varepsilon)t}\big(\beta - p(t,x)\big) = 0 \quad\text{and, for some } i,\quad \lim_{t\to\infty}\ \sup_{|x| \ge (c^*+\varepsilon)t} p_i(t,x) = 0,$$

and the **fastest spreading speed** $c^*_f$ by: for every $\varepsilon > 0$,

$$\lim_{t\to\infty}\ \sup_{|x| \ge (c^*_f+\varepsilon)t} p(t,x) = 0 \quad\text{and, for some } i,\quad \limsup_{t\to\infty}\ \inf_{|x| \le (c^*_f-\varepsilon)t} p_i(t,x) > 0$$

(the source's (5)–(6)); $c^* \le c^*_f$. Put $f'(0) + \mu^2 D$ in Frobenius (block lower-triangular) form with diagonal-block principal eigenvalues $\gamma_i(\mu)$ and eigenvectors $\zeta_i(\mu)$, and define the linear speeds $c_i = \inf_{\mu > 0} \gamma_i(\mu)/\mu$, $c_f = \max_i c_i$.

**Theorem.** Assume

- (I) $\gamma_1(0) > 0$ with $\zeta_1(0) \gg 0$.

Then $c^*$ and $c^*_f$ exist and $c^* \ge c_1$, $c^*_f \ge c_f$. If in addition

- (II) $\gamma_1(\bar\mu) > \gamma_i(\bar\mu)$ for $i > 1$, where $\bar\mu$ attains $\inf_{\mu>0} \mu^{-1}\gamma_1(\mu)$, and
- (III) $f(\rho\, \zeta_1(\bar\mu)) \le \rho\, f'(0)\, \zeta_1(\bar\mu)$ for all $\rho > 0$,

then the system has a single spreading speed and is **linearly determinate**:

$$
c^*_f = c^* = c_f = c_1 = \inf_{\mu > 0} \frac{\gamma_1(\mu)}{\mu}.
$$

## Expansion

Condition (I) says there is a single invading block that grows at zero density; (II) says its minimal linear speed dominates those of all other blocks; (III) rules out Allee-type growth along the invader's eigenvector. Under (III) the exponential profile $\rho e^{-\bar\mu(x - c_1 t)} \zeta_1(\bar\mu)$ is a supersolution, giving $c^*_f \le c_1$, while (I) and comparison with the linearized system give the lower bound. In the scalar Fisher–KPP case this reduces to $c^* = 2\sqrt{f'(0) D}$.

## Sources

- Hans F. Weinberger, Mark A. Lewis, Bingtuan Li, "Analysis of linear determinacy for spread in cooperative models", Journal of Mathematical Biology 45 (2002), 183–218, <https://doi.org/10.1007/s002850200145>. The linear-determinacy theorem for cooperative reaction–diffusion systems.
- Volodymyr Hrynkiv, Sergiy Koshkin, "Invasion waves in the presence of a mutualist", Mathematical Methods in the Applied Sciences 37 (2014), 2185–2197, <https://doi.org/10.1002/mma.2964>. Published version of arXiv:1705.05474, cited next; locators there refer to the arXiv version.
- Volodymyr Hrynkiv, Sergiy Koshkin, "Invasion waves in the presence of a mutualist", arXiv (2017). Theorem 1 (from Weinberger, Lewis and Li). <https://doi.org/10.48550/arXiv.1705.05474>
