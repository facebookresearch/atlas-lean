# Resolvent characterization of finite Koopman spectral expansions

Let $(X_x(t))_{t\ge 0}$ be the continuous-time Markov chain of a stochastic reaction network on a countable state space $\mathcal{E} \subseteq \mathbb{Z}^D_{\ge 0}$ started at $x$, assumed exponentially ergodic with stationary distribution $\pi$, and with generator $\mathbb{A}$. For observables $f \in \mathcal{L}_2(\pi)$ (for example copy-number moments $f(y) = y_k^j$) the *Koopman operator* is $\mathcal{K}_t f(x) = \mathbb{E}[f(X_x(t))] = e^{t\mathbb{A}} f$, and for $s \in \mathbb{C}_+ = \{\operatorname{Re} s > 0\}$ the *resolvent* is

$$\mathcal{R}_s f(x) = \int_0^\infty s\, e^{-st}\, \mathcal{K}_t f(x)\, dt.$$

$\mathcal{K}_t$ has eigenvalue $e^{-\sigma t}$ with eigenfunction $\phi$ if and only if $\mathcal{R}_s$ has eigenvalue $s/(s+\sigma)$ with the same eigenfunction, and $\lim_{s \to 0} \mathcal{R}_s f(x) = \mathbb{E}_\pi(f)$.

**Theorem.** Let $\sigma_1,\dots,\sigma_J \in \mathbb{C}_+$ and let $f$ be an observable with stationary mean $\mathbb{E}_\pi(f)$. The finite spectral expansion

$$\mathcal{K}_t f(x) = \mathbb{E}_\pi(f) + \sum_{j=1}^J \alpha_j(f,x)\, e^{-\sigma_j t} \qquad \text{for all } t \ge 0,\ x \in \mathcal{E},$$

holds if and only if for some $s \in \mathbb{C}_+$

$$\frac{\prod_{j=1}^J \big( s(\mathcal{R}_s - \mathbf{I}) + \sigma_j \mathcal{R}_s \big)}{\prod_{j=1}^J \sigma_j}\, f(x) = \mathbb{E}_\pi(f) \qquad \text{for all } x \in \mathcal{E}.$$

If the condition holds for one $s \in \mathbb{C}_+$ it holds for all of them, and then for any $s \in \mathbb{C}_+$

$$\alpha_j(f,x) = \frac{s + \sigma_j}{\sigma_j} \sum_{k=1}^J \mathbf{L}_{jk}(s)\, \big(\mathcal{R}_s^{k-1} - \mathcal{R}_s^{k}\big) f(x),$$

where $\mathbf{L}(s)$ is the $J \times J$ Lagrange interpolation matrix with nodes $s/(s+\sigma_j)$ (row $j$ holds the coefficients of the $j$-th Lagrange basis polynomial). Each nonzero $\alpha_j(f,\cdot)$ is an eigenfunction, $\mathcal{R}_s \alpha_j = \frac{s}{s+\sigma_j} \alpha_j$, equivalently $\mathbb{A} \alpha_j = -\sigma_j \alpha_j$.

Since the condition does not involve the coefficients, decay modes can be identified first (in practice by minimizing the residual of the condition over candidate $\sigma$'s, a convex problem evaluated with Monte Carlo estimates of resolvent iterates) and coefficients afterwards by the explicit formula. For the constitutive gene-expression network (mRNA birth $k_r$, decay $\gamma_r$, protein production $k_p$, decay $\gamma_p$) the expansion is exact with modes $\gamma_r, \gamma_p$.

## Expansion

Applying $\mathcal{R}_s$ to $e^{-\sigma_j t}$ terms gives $\frac{s}{s+\sigma_j}$, so $s(\mathcal{R}_s - \mathbf{I}) + \sigma_j \mathcal{R}_s$ annihilates the $j$-th mode and maps the constant $\mathbb{E}_\pi(f)$ to $\sigma_j \mathbb{E}_\pi(f)$; the product of these factors therefore kills all $J$ modes and leaves $\prod_j \sigma_j\, \mathbb{E}_\pi(f)$. Conversely, the condition says $f - \mathbb{E}_\pi(f)$ lies in the sum of the eigenspaces of $\mathcal{R}_s$ for the eigenvalues $s/(s+\sigma_j)$, which are independent of $s$ as eigenspaces of $\mathbb{A}$; this yields the time-domain expansion. The resolvent iterates satisfy $\mathcal{R}^m_s f(x) = \frac{s^m}{(m-1)!} \int_0^\infty t^{m-1} e^{-st} \mathcal{K}_t f(x)\, dt$, and the projection onto each eigenspace is a Lagrange interpolation in the variable $s/(s+\sigma)$, giving the coefficient formula.

## Sources

- Ankit Gupta, Mustafa Khammash, "A Spectral Koopman Approximation Framework for Stochastic Reaction Networks", arXiv:2511.23114 (2025), Theorem 3.1 and the supplementary proposition on properties of the resolvent operator, <https://doi.org/10.48550/arXiv.2511.23114>
