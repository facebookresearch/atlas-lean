# Central limit theorems for the allelic frequency spectrum of a splitting tree

**Setting.** As in [the almost-sure limit](almost-sure-limit-of-the-allelic-frequency-spectrum-of-a-splitting-tree.md): a supercritical splitting tree with lifetime law $\mathbb{P}_V$, birth rate $b$, Malthusian parameter $\alpha > 0$ and Laplace exponent $\psi$, neutral Poissonian mutations at rate $\theta$ under infinitely many alleles, population size $N_t$, frequency spectrum $A(k,t)$, martingale limit $\mathcal{E}$ and limiting constants $c_k$ (the number of size-$k$ families per individual, defined there with the factor $W_\theta(a)^{-2}$). All statements are under $\mathbb{P}_\infty$ (conditioned on survival), and $\mathcal{L}(0,K)$ denotes the centered Laplace law with covariance parameter $K$ (here on sequences indexed by $k \in \mathbb{N}$, in the sense of finite-dimensional distributions): the law with characteristic function $\lambda\mapsto\bigl(1+\tfrac12\lambda^\top K\lambda\bigr)^{-1}$, that is, the law of $\sqrt{\mathcal{E}'}\,G$ with $G$ a centered Gaussian vector with covariance $K$ and $\mathcal{E}'\sim\mathrm{Exp}(1)$ independent of $G$.

**Theorem (error of the random-limit approximation).** Assume the clonal subcritical regime $\theta > \alpha$ and $\int_{[0,\infty)} e^{(\theta-\alpha)v}\,\mathbb{P}_V(dv) > 1$. Then

$$\Big(e^{-\alpha t/2}\big(\psi'(\alpha)A(k,t) - e^{\alpha t}c_k\,\mathcal{E}\big)\Big)_{k\in\mathbb{N}} \xrightarrow[t\to\infty]{(d)} \mathcal{L}(0,K)$$

for some covariance matrix $K$.

**Theorem (error of the proportional approximation).** Assume only $\theta > \alpha$. Then

$$\psi'(\alpha)\Big(e^{-\alpha t/2}\big(A(k,t) - c_k N_t\big)\Big)_{k\in\mathbb{N}} \xrightarrow[t\to\infty]{(d)} \mathcal{L}(0,M),$$

where, writing $\mathbb{P}_a = \mathbb{P}(\,\cdot \mid N_a > 0)$ with expectation $\mathbb{E}_a$, $Z_0(a)$ for the size at time $a$ of the clonal family (the individuals still carrying the ancestral type, which $A(k,\cdot)$ excludes), and $q_\theta(a) = 1 - 1/W_\theta(a)$, the covariance $M$ is (Henry's (3.1))

$$\begin{aligned} M_{l,k} ={}& 2\psi'(\alpha)\int_0^\infty \frac{\theta e^{-\theta a}}{W_\theta(a)^2}\Big(q_\theta(a)^{l-1}\big(\mathbb{E}_a[A(k,a)] - c_k W(a)\big) + q_\theta(a)^{k-1}\big(\mathbb{E}_a[A(l,a)] - c_l W(a)\big)\Big)\,da \\ &- \psi'(\alpha)\int_0^\infty \frac{\theta}{W(a)}\,\mathbb{E}_a\Big[\big(A(k,a) - c_k N_a\big)\mathbf{1}_{\{Z_0(a) = l\}} + \big(A(l,a) - c_l N_a\big)\mathbf{1}_{\{Z_0(a) = k\}}\Big]\,da \\ &+ \mathbf{1}_{\{l = k\}}\int_0^\infty \frac{\theta e^{-\theta s}}{W_\theta(s)^2}\,q_\theta(s)^{k-1}\,ds . \end{aligned}$$

The finite-time mean is explicit, $\mathbb{E}_a[A(k,a)] = W(a)\int_0^a \frac{\theta e^{-\theta s}}{W_\theta(s)^2}\,q_\theta(s)^{k-1}\,ds$.

**Markovian case.** If $V$ is exponential with parameter $d \in [0,b)$, so that $\alpha = b - d < \theta$ is assumed, the first theorem holds with

$$K_{l,k} = M_{l,k} + c_k c_l\,\frac{\alpha}{b}\Big(1 - 6\,\frac{d}{\alpha}\Big),$$

where $M$ is the same matrix (3.1) displayed above.

Both approximations therefore have fluctuations of order $e^{\alpha t/2}$, the square root of the population size, with a Gaussian variance mixture as limit: the population at time $t$ is about $\mathcal{E}e^{\alpha t}$ with $\mathcal{E}$ exponential under $\mathbb{P}_\infty$, so on the deterministic scale $e^{\alpha t/2}$ the Gaussian fluctuations carry a random variance proportional to $\mathcal{E}$; replacing the unknown limit $\mathcal{E}$ by the observed $N_t$ removes the extra rank-one term in the covariance.

## Depends on

- [Almost-sure limit of the allelic frequency spectrum of a splitting tree](almost-sure-limit-of-the-allelic-frequency-spectrum-of-a-splitting-tree.md)

## Expansion

Decompose the population at an intermediate time $u = \beta t$: by the residual-lifetime lemma, the subtrees of the $N_u$ individuals alive at $u$ are independent and identically distributed (except the ancestor's), and $\mathcal{E} = e^{-\alpha u}\sum_{i=1}^{N_u}\mathcal{E}_i(O_i)$. When $\theta > \alpha$, with probability tending to one no family alive at $t$ is older than $\beta t$ for $\beta < 1 - \alpha/\theta$, so the spectrum at $t$ is a sum of $N_u$ nearly independent contributions. A Lindeberg-type CLT applies once the second moments are identified through renewal equations (Lemmas 4.3–4.5) and third or fourth moments are bounded. The exponential case is computed explicitly, and in simulations the proportional approximation $c_k N_t$ is compared with the extended haplotype homozygosity statistic.

## Sources

- Benoit Henry, "Approximation of the allelic frequency spectrum in general supercritical branching populations", *Stochastic Process. Appl.* 132 (2021), 192-225. <https://doi.org/10.1016/j.spa.2020.10.008>
- Preprint version (the locators in this item follow its numbering): Benoit Henry, "Approximations of the allelic frequency spectrum in general supercritical branching populations", arXiv:1701.07281 (2017), Theorems 3.1, 3.3 and 3.5, Equation (3.1) for $M$, Equation (2.11) for $\mathbb{E}_t A(k,t)$, Lemmas 4.1–4.11, <https://doi.org/10.48550/arXiv.1701.07281>. The preprint prints the normalization $e^{\alpha t/2}$ in Theorems 3.1, 3.3 and 3.5; this is a sign misprint, since its Lemma 4.5 gives $\lim_{t\to\infty}e^{-\alpha t}\,\mathbb{E}\big[(\psi'(\alpha)A(k,t)-e^{\alpha t}\mathcal{E}c_k)(\psi'(\alpha)A(l,t)-e^{\alpha t}\mathcal{E}c_l)\big]=\frac{\alpha}{b}a_{k,l}$, so the errors are of order $e^{\alpha t/2}$ and the normalization that converges is $e^{-\alpha t/2}$, used above.
