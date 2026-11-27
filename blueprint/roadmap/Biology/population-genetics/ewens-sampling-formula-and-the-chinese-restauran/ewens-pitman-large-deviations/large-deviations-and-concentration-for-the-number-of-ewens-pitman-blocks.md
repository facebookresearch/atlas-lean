# Large deviations and concentration for the number of blocks in the Ewens–Pitman model

**Model.** The Ewens–Pitman (two-parameter Chinese restaurant) model with $\alpha \in [0,1)$ and $\theta > -\alpha$ is the exchangeable random partition of $\{1,\dots,n\}$ built sequentially: given $k$ blocks of sizes $n_1,\dots,n_k$ among the first $m$ elements, element $m+1$ starts a new block with probability $\frac{\theta + k\alpha}{\theta + m}$ and joins block $j$ with probability $\frac{n_j - \alpha}{\theta + m}$. For $\alpha = 0$ it is the Ewens sampling formula of neutral population genetics (blocks are allelic types in a sample of $n$ genes, $\theta$ the scaled mutation rate). Let $K_n$ be the number of blocks; for $\alpha \in (0,1)$, $K_n/n^\alpha$ converges almost surely to a Mittag-Leffler type limit, so $K_n/n \to 0$.

**Theorem (Feng–Hoppe large deviation principle).** For $\alpha \in (0,1)$ and $\theta > -\alpha$, $(K_n/n)_{n \ge 1}$ satisfies a large deviation principle with good rate function

$$I_\alpha(x) = \sup_{t \in \mathbb{R}}\{xt - L_\alpha(t)\}, \qquad L_\alpha(t) = \begin{cases} -\log\big(1 - (1 - e^{-t})^{1/\alpha}\big) & t > 0,\\ 0 & t \le 0,\end{cases}$$

independent of $\theta$.

**Theorem (concentration inequality).** For $\alpha \in (0,1)$, $\theta > -\alpha$, every $x \in (0,1)$ and every $n \ge 1$,

$$\mathbb{P}\Big(\frac{K_n}{n} \ge x\Big) \le \frac{P_n(\alpha,\theta)\,c_n(\alpha,\theta)}{\alpha}\,e^{-nI_\alpha(x)},$$

where $P_n(\alpha,\theta) = (\lfloor\theta/\alpha\rfloor + n)^{\theta/\alpha}$ if $\theta > 0$ and $P_n = 1$ if $\theta \le 0$, and

$$c_n(\alpha,\theta) = \frac{\Gamma(n)\,\Gamma(\theta + 1)}{\Gamma(\theta/\alpha + 1)\,\Gamma(n + \theta)};$$

for $\theta = 0$ the prefactor $P_n c_n/\alpha$ reduces to $1/\alpha$. The prefactor grows at most polynomially in $n$, so the bound has the exact LDP exponent.

## Expansion

For $\theta = 0$ the moment generating function of $K_n$ has an integral representation in terms of the one-parameter Mittag-Leffler function $E_\alpha$, and a sharp asymptotic expansion of $E_\alpha$ gives $\frac1n\log\mathbb{E}e^{tK_n} \to L_\alpha(t)$; the Gärtner–Ellis theorem then yields the LDP, and Chernoff's bound with the exact (non-asymptotic) moment generating function gives the concentration inequality. The case $\theta \neq 0$ reduces to $\theta = 0$ through Pitman's change-of-measure formula linking $\mathbb{P}_{\alpha,\theta}$ to $\mathbb{P}_{\alpha,0}$; it contributes only the prefactor $P_n c_n$ and leaves the exponential rate unchanged.

## Sources

- Bernard Bercu and Stefano Favaro, "A new look on large deviations and concentration inequalities for Ewens-Pitman model", *Bollettino dell'Unione Matematica Italiana* (2026), <https://doi.org/10.1007/s40574-026-00537-3>. Numbering as in the preprint arXiv:2503.06783v1, <https://arxiv.org/abs/2503.06783v1>: Theorems 1.1–1.2 and Lemmas 2.1–2.2.
