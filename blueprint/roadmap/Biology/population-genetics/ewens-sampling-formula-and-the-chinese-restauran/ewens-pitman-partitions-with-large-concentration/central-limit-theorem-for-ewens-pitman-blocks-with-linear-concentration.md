# Central limit theorem for Ewens–Pitman blocks with linearly growing concentration

**Setting.** The Ewens–Pitman model with discount $\alpha \in [0,1)$ and concentration $\theta > -\alpha$ generates a random partition of $\{1,\dots,n\}$ sequentially: given $k$ blocks of sizes $n_1,\dots,n_k$ among the first $m$ elements, element $m+1$ joins block $i$ with probability $(n_i - \alpha)/(\theta + m)$ and starts a new block with probability $(\theta + k\alpha)/(\theta + m)$. For $\alpha = 0$ this is the Ewens sampling formula of population genetics (with $\theta$ the scaled mutation rate). Let $K_n$ be the number of blocks (distinct alleles or species in a sample of size $n$).

**Theorem.** Let $\theta = \lambda n$ with fixed $\lambda > 0$. Define

$$\mathfrak m_{\alpha,\lambda} = \begin{cases}\dfrac{\lambda}{\alpha}\Big[\big(1 + \tfrac1\lambda\big)^\alpha - 1\Big], & \alpha \in (0,1),\\[2mm] \lambda\log\big(1 + \tfrac1\lambda\big), & \alpha = 0,\end{cases}$$

$$\mathfrak s^2_{\alpha,\lambda} = \begin{cases}\dfrac{\lambda}{\alpha}\Big[\big(1 + \tfrac1\lambda\big)^{2\alpha}\big(1 - \tfrac{\alpha}{1+\lambda}\big) - \big(1 + \tfrac1\lambda\big)^{\alpha}\Big], & \alpha \in (0,1),\\[2mm] \lambda\log\big(1 + \tfrac1\lambda\big) - \dfrac{\lambda}{\lambda+1}, & \alpha = 0.\end{cases}$$

Then, as $n \to \infty$, $\mathbb E[K_n] = n\,\mathfrak m_{\alpha,\lambda} + O(1)$, $\operatorname{Var}(K_n) = n\,\mathfrak s^2_{\alpha,\lambda} + O(1)$,

$$\frac{K_n}{n} \xrightarrow{p} \mathfrak m_{\alpha,\lambda}, \qquad \frac{K_n - n\,\mathfrak m_{\alpha,\lambda}}{\sqrt{n\,\mathfrak s^2_{\alpha,\lambda}}} \xrightarrow{w} \mathcal N(0,1),$$

and the $\alpha = 0$ constants are the limits of the $\alpha > 0$ ones as $\alpha \to 0^+$.

## Expansion

For fixed $\theta$, $K_n$ grows like $\theta\log n$ ($\alpha = 0$) or like $n^\alpha$ times a non-degenerate random variable ($\alpha > 0$), with no Gaussian fluctuations in the latter case. When the concentration grows linearly with the sample, new blocks keep appearing at a positive rate and $K_n$ becomes linear in $n$ with Gaussian fluctuations. For $\alpha = 0$, $K_n$ is a sum of independent Bernoulli variables with success probabilities $\lambda n/(\lambda n + i - 1)$, whose mean and variance give the stated constants directly. For $\alpha > 0$ the proof represents $K_n$ through a randomized compound of Gamma variables and a negative-binomial-type count, proving a law of large numbers and CLT for the randomizing variable and a Berry–Esseen bound conditionally on it.

## Sources

- Claudia Contardi, Emanuele Dolera and Stefano Favaro, "Laws of large numbers and central limit theorem for Ewens-Pitman model", Electron. J. Probab. 30 (2025), 1–51, <https://doi.org/10.1214/25-EJP1457>. Numbering follows the arXiv version, arXiv:2412.11493 (2024): Theorem 1.2 and Propositions 2.1–2.3, <https://doi.org/10.48550/arXiv.2412.11493>.
