# Observability threshold of real-time PCR

Let $Z_n$ be the number of DNA molecules after $n$ PCR cycles, started from $Z_0$, with

$$Z_n = Z_{n-1} + \sum_{j=1}^{Z_{n-1}} \xi_{n,j}, \qquad P(\xi_{n,j} = 1 \mid \mathcal F_{n-1}) = \frac{vK}{K + Z_{n-1}},$$

where, given $\mathcal F_{n-1} = \sigma(Z_0, \dots, Z_{n-1})$, the indicators $\xi_{n,1}, \xi_{n,2}, \dots \in \{0,1\}$ are conditionally independent (in the source, $\xi_{n,j} = \mathbf 1\{U_{n,j} \le vK/(K + Z_{n-1})\}$ for i.i.d. uniforms $U_{n,j}$ indexed by step and molecule), $v \in (0,1]$ is the maximal replication efficiency and $K$ is a large Michaelis–Menten constant. Let $X_n = Z_n/K$ be the density process, $b = 1 + v$, and

$$f(x) = x + \frac{v x}{1 + x} = E(X_n \mid X_{n-1} = x).$$

**Fixed-horizon law of large numbers.** Let the initial count $Z_0 = Z_0^{(K)}$ depend on $K$ with initial density $X_0 = Z_0/K \to x_0$ as $K \to \infty$. Then $X_n \to f^n(x_0)$ in probability for each fixed $n$. In particular, for a fixed initial count $Z_0$ (the setting of the rest of this page), $x_0 = 0$ and $f^n(0) = 0$, so at any fixed cycle the reaction is not observable in the limit.

**Linear replication limit.** The process $Y_n$ in which each molecule duplicates independently with constant probability $v$ is Galton–Watson with mean $b$, and $W = \lim_n b^{-n}Y_n$ exists a.s. with $E W = 1$ for $Y_0 = 1$; its Laplace transform $\phi(s) = E e^{-sW}$ is the unique solution of $\phi(bs) = (1-v)\phi(s) + v\phi(s)^2$ with $\phi'(0) = -1$. Starting from $Z_0$ molecules, $W(Z_0) = \sum_{i=1}^{Z_0} W_i$ with $W_i$ i.i.d. copies of $W$.

**The function $H$.** The limit $H(x) = \lim_{n\to\infty} f^n(x/b^n)$ exists, is continuous and strictly increasing on $[0,\infty)$, and solves Schröder's equation $H(x) = f(H(x/b))$.

**Theorem.** Let the initial count $Z_0$ be fixed. Along $K \to \infty$ with $\log_b K$ an integer,

$$X_{\log_b K} \xrightarrow{\ D\ } H\bigl(W(Z_0)\bigr),$$

and more generally $\{X_{\log_b K + n}\}_{n\in\mathbb Z} \to \{f^n(H(W(Z_0)))\}_{n\in\mathbb Z}$ in distribution as random sequences. For general $K$, $X_{\lfloor\log_b K\rfloor} - H\bigl(W(Z_0)\,b^{\lfloor\log_b K\rfloor - \log_b K}\bigr) \to 0$ in distribution.

For $v = 1$ the early phase is deterministic, $W(Z_0) = Z_0$, and the initial number can be recovered by inverting $H$. For $v < 1$ the limit is a continuous random variable with positive variance, and the random early phase blurs the information about $Z_0$.

## Expansion

While $Z_n \ll K$ the replication probability is close to $v$, so $Z_n$ tracks the linear process and $Z_{n_1} \approx W(Z_0)\,b^{n_1}$ at $n_1 = c\log_b K$ with $c < 1$. From there the density is small but macroscopic enough for the law of large numbers, so $X_{\log_b K} \approx f^{(1-c)\log_b K}\bigl(W b^{-(1-c)\log_b K}\bigr) \to H(W)$. The coupling error is controlled by comparison with the linear process, a maximal inequality $P(\sup_{n<n_1} Y_n b^{-n} > K^{\gamma - c}) \le K^{c-\gamma}$, and the Lipschitz bound $|f^n(x) - f^n(y)| \le b^n|x - y|$ that follows from concavity of $f$ with $f'(0) = b$. The detection threshold cycle therefore sits near $\log_{1+v} K$, shifted by $\log_b$ of the random factor $W(Z_0)$. This is the mathematical form of the quantification-cycle principle of real-time PCR.

## Sources

- P. Chigansky, P. Jagers, F. C. Klebaner, "What can be observed in real time PCR and when does it show?", Journal of Mathematical Biology (2018), Eqs. (1)–(9), Theorems 1–2, Remarks 1–2 and Corollary 1, <https://doi.org/10.1007/s00285-017-1154-1>, PMCID PMC5772144.
