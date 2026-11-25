# Arm mem Lp integral sq

Let $\mu$ be a finite measure on $\Omega$, $X : \Omega \to \mathcal{X}$ measurable, and write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$. Let $S \subseteq \Omega$ be measurable, $p : \mathcal{X} \to \mathbb{R}$ measurable with $p(x) \ge \varepsilon$ for every $x$ and some $\varepsilon > 0$, $s : \mathcal{X} \to \mathbb{R}$, and $R \in L^2(\mu)$ with

$$\mathbb{E}[\mathbf{1}_S R^2 \mid X] = p(X)\, s(X) \quad \mu\text{-a.e.}$$

Then $\mathbf{1}_S R / p(X) \in L^2(\mu)$, $s(X)/p(X)$ is integrable, and

$$\int_\Omega \left(\mathbf{1}_S \frac{R}{p(X)}\right)^2 d\mu = \int_\Omega \frac{s(X)}{p(X)}\, d\mu.$$
