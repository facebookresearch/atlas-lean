# Expected frequencies of two quasispecies under rare sudden mutations

**Model.** Types $0,\dots,D$ have frequencies $x_t$ on the simplex and nonnegative Lipschitz fitness functions $f_k(x)$, with $f(x) = (f_0(x),\dots,f_D(x)) \ne 0$ on the simplex. Instead of the continuous mutation term of the quasispecies equation, mutations from $i$ to $k$ arrive as jumps of point processes $N^{ik}$ with intensity $\lambda_{ik}f_i(x_{t^-})$, where $\lambda_{ik} > 0$, each transferring a fixed proportion $\gamma_{ik} \in (0,1]$ of type $i$ to type $k$:

$$dx^k_t = \big(f_k(x_t) - \bar f(x_t)\big)x^k_t\,dt + \sum_{i\ne k}\gamma_{ik}x^i_{t^-}\,dN^{ik}_t - \sum_{i\ne k}\gamma_{ki}x^k_{t^-}\,dN^{ki}_t.$$

The process is well defined, and the expected frequencies $u_k(x,t) = \mathbb E[x^k_t \mid x_0 = x]$ solve the nonlocal first-order Kolmogorov equation $\partial_t u_k + a(x)\cdot\nabla u_k = \mathcal J u_k$, $u_k(x,0) = x_k$, with $a_k(x) = -(f_k - \bar f)x_k$ and $\mathcal J\phi(x) = \sum_{i\ne j}\lambda_{ij}f_i(x)\big[\phi(x + \gamma_{ij}x_i(e_j - e_i)) - \phi(x)\big]$; it has a unique global mild solution, which coincides with the viscosity solution, satisfies a comparison principle, and is Lipschitz in $x$.

**Two types, constant fitness.** Let $f_0 > f_1 > 0$, $\sigma = f_0 - f_1 > 0$, $x$ the frequency of the less fit type $1$, $\gamma_0 = \gamma_{01}$, $\gamma_1 = \gamma_{10}$, $\lambda_0 = \lambda_{01}$, $\lambda_1 = \lambda_{10}$, and $m_i = \lambda_i\gamma_i$. Here the rates may vanish: $\lambda_{ik} \ge 0$, so $\lambda_0, \lambda_1 \ge 0$ and $m_0, m_1 \ge 0$ (with constant fitness each $N^{ik}$ is a Poisson process of rate $\lambda_{ik}f_i$, so the process is well defined directly also when a rate is $0$). Then $u(x,t) = \mathbb E[x_t \mid x_0 = x]$ solves

$$\partial_t u + \sigma x(1-x)\,\partial_x u = \lambda_0 f_0\big[u(x + \gamma_0(1-x),t) - u\big] + \lambda_1 f_1\big[u((1-\gamma_1)x,t) - u\big], \qquad u(x,0) = x,$$

to be compared with the deterministic quasispecies flow $X(x,t)$ of $\dot x = -\sigma x(1-x) + m_0f_0(1-x) - m_1f_1x$.

**Proposition.**

1. $1 \ge u(x,t) \ge X(x,t)$ for all $x \in [0,1]$, $t \ge 0$: rare sudden mutations raise the expected frequency of the less fit type relative to the quasispecies equation with the same mean mutation rates.
2. $\bar u(x) = \lim_{t\to\infty}u(x,t)$ exists for every $x$, and is constant if $m_1 > 0$, or if $m_1 = 0$ and $m_0 \ge \sigma/f_0$.
3. (*Fair mutation*, $m_0 = 0 < m_1$.) $\bar u = 0$, and

$$\frac{x\,e^{-\sigma t}}{1 - x(1-e^{-\sigma t})} \ \ge\ u(x,t) \ \ge\ \frac{x\,e^{-(\sigma + m_1f_1)t}}{1 - \frac{\sigma x}{\sigma + m_1f_1}\big(1 - e^{-(\sigma + m_1f_1)t}\big)}.$$

4. (*Strong unfair mutation*, $m_1 = 0$, $m_0 \ge \sigma/f_0$.) $\bar u = 1$, with $u(x,t) \ge 1 - \dfrac{1-x}{1 + \frac{\sigma(1-x)}{m_0f_0 - \sigma}\big(e^{(m_0f_0-\sigma)t} - 1\big)}$ if $m_0 > \sigma/f_0$ and $u(x,t) \ge 1 - \dfrac{1-x}{1 + \sigma(1-x)t}$ if $m_0 = \sigma/f_0$.

## Expansion

Along the characteristics of the replicator drift the Kolmogorov equation becomes an integral equation, giving the mild solution; the jump operator is monotone, which yields the comparison principle. Since $x \mapsto u(x,t)$ is convex (its second derivative is nonnegative), Jensen's inequality shows that replacing the jump by its mean, which is what the deterministic quasispecies term does, can only lower the expected frequency, giving $u \ge X$. The explicit bounds come from comparing $u$ with logistic-type sub- and supersolutions whose rates bracket the effective selection $\sigma$ and the combined rate $\sigma + m_1f_1$.

## Sources

- Anna Lisa Amadori, Antonella Calzolari, Roberto Natalini, Barbara Torti, "Rare mutations in evolutionary dynamics", *Journal of Differential Equations* 259 (2015), 6191–6214, <https://doi.org/10.1016/j.jde.2015.07.021>; preprint arXiv:1211.4170, <https://doi.org/10.48550/arXiv.1211.4170>. Numbering of the arXiv version: Section 2 (stochastic model, Lemma 2.1, Proposition 2.1), Section 3 (Kolmogorov equation, Propositions 3.1–3.5), Section 4 (two quasispecies, Lemmas 4.1–4.3, Propositions 4.1–4.5).
