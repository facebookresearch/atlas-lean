# Absorption probabilities with killing versus stationary tails with catastrophes

**Setting.** Fix $N \in \mathbb N \cup \{\infty\}$, $\kappa > 0$ and positive sequences $(\lambda_i)$, $(\mu_i)$. A *birth–death process with killing* $X$ on $\{0, \dots, N\} \cup \{\Delta\}$ jumps $i \to i+1$ at rate $i\lambda_i$, $i \to i-1$ at rate $i\mu_i$, and $i \to \Delta$ (killing) at rate $i\kappa$; let $b_i = \mathbb P_i(X \text{ is absorbed at } 0)$. The *paired birth–death process with catastrophes* $Z$ on $\{1, \dots, N-1\}$ jumps $i \to i+1$ at rate $i\lambda_{i+1}$, $i \to i-1$ at rate $(i-1)\mu_{i+1} + \kappa$, and $i \to j$ at rate $\kappa$ for every $j \le i-2$ (a catastrophe); let $a_i = \mathbb P(Z_{\mathrm{eq}} > i)$ be its stationary tail probabilities.

**Theorem.** (For $N = \infty$, assume $\sum_{i\ge1}1/\lambda_i = \infty$ and $\sum_{i\ge1}1/\mu_i = \infty$.) $Z$ has an equilibrium distribution and

$$\frac{b_i}{b_2} = \frac{a_{i-2} - a_{i-1}}{a_0 - a_1}\prod_{j=1}^{i-2}\frac{\mu_{j+2}}{\lambda_{j+1}}, \quad 2 \le i \le N, \qquad a_i = \frac{b_{i+1} - b_{i+2}}{b_1 - b_2}\prod_{j=1}^{i}\frac{\lambda_{j+1}}{\mu_{j+1}}, \quad 0 \le i \le N-2.$$

Equivalently, the $a_i$ solve $(\mu_{i+1} + \lambda_i + \kappa)a_i = \lambda_i a_{i-1} + \mu_{i+1}a_{i+1}$ with $a_0 = 1$, the same type of first-step recursion as $(\lambda_i + \mu_i + \kappa)b_i = \lambda_i b_{i+1} + \mu_i b_{i-1}$ with $b_0 = 1$. In addition, $\mathbb P_{n+1}(X \text{ hits } n) = \dfrac{\mathbb P(Z_{\mathrm{eq}} = n)}{\mathbb P(Z_{\mathrm{eq}} = n-1)}\cdot\dfrac{\mu_{n+1}}{\lambda_n}$.

**Application.** With $\lambda_i = \sigma$, $\mu_i = i - 1 + \vartheta\nu_1$, $\kappa = \vartheta\nu_0$ (diffusion limit of a Moran model with selection strength $\sigma$ and two-way mutation at rates $\vartheta\nu_0, \vartheta\nu_1$), $X$ is the line-counting process of the killed ancestral selection graph and $Z$ that of the pruned lookdown ancestral selection graph; the identities relate the absorption probabilities $\beta_i$ of the former to the tail probabilities $\alpha_i$ of the latter, which give the ancestral type distribution.

## Expansion

Two ingredients connect the processes. A Feynman–Kac-type identity for Markov chains with reset and rebirth shows that killing at rate $\kappa$ biases the stationary weights of a reset chain by $\mathbb E[e^{-\kappa T}]$, which turns killing into catastrophes. Siegmund duality, $\mathbb P(Z_t \ge j \mid Z_0 = i) = \mathbb P(Z^\star_t \le i \mid Z^\star_0 = j)$, then converts stationary tails of a process with catastrophes into absorption probabilities of a birth–death process with killing; composing the two and decomposing the dynamics at the first downward step gives the product formulas.

## Sources

- Ellen Baake, Fernando Cordero, Enrico Di Gaspero and Anton Wakolbinger, "Killing versus catastrophes in birth–death processes and an application to population genetics", J. Appl. Probab. (2026), online first, <https://doi.org/10.1017/jpr.2026.10131>. Numbering follows the arXiv version, arXiv:2407.08478 (2024): Theorem 1.2, Propositions 2.1, 3.1 and 5.1, Corollaries 5.2 and 6.1, <https://doi.org/10.48550/arXiv.2407.08478>.
