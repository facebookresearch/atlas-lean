# Limit law of the quartet balance index under Aldous's beta-splitting model

**Quartet index.** For a rooted binary phylogenetic tree $T$ with $n$ leaves, every set of four leaves induces a rooted quartet, which is either the caterpillar $K_4$ or the fully balanced tree $B_4$. The quartet index of a binary tree is

$$ QIB(T) = \#\{ \text{four-leaf subsets inducing } B_4 \}, $$

a balance index that is larger for more balanced trees. If the root of $T_n$ splits the leaves into subtrees of sizes $L_n$ and $n - L_n$, then for $n > 4$, $QIB(T_n) = QIB(T_{L_n}) + QIB(T_{n-L_n}) + \binom{L_n}{2} \binom{n - L_n}{2}$.

**Aldous's $\beta$-splitting model.** A tree on $n$ leaves is generated recursively: the root splits into subtrees of sizes $i$ and $n-i$ with probability proportional to $\frac{\Gamma(\beta + i)\Gamma(\beta + n - i)}{\Gamma(i)\Gamma(n-i)}$, $1 \le i \le n-1$ (equivalently $L_n - 1 \sim \mathrm{BetaBinomial}(n-2, \beta+1, \beta+1)$), and each subtree is generated independently. For $\beta > -1$, $L_n / n$ converges in distribution to $\tau \sim \mathrm{Beta}(\beta + 1, \beta + 1)$; $\beta = 0$ is the Yule model. For $\beta \ge 0$, $\mathbb{E}\, QIB(T_n) = \frac{3\beta + 6}{7\beta + 18} \binom{n}{4}$.

**Theorem 4.1.** Let $\beta \ge 0$ and

$$ Y_n^Q = n^{-4} \Bigl( QIB(T_n) - \frac{3\beta + 6}{7\beta + 18} \binom{n}{4} \Bigr). $$

Then $Y_n^Q$ converges, in the Wasserstein metric $d_2$ and hence in distribution, to a random variable $Y_Q$ whose law $\mathcal{Q}$ is the unique fixed point (with mean zero and finite variance) of the distributional equation

$$ Y_Q \overset{d}{=} \tau^4 Y_Q' + (1 - \tau)^4 Y_Q'' + \frac{3\beta + 6}{24(7\beta + 18)} \bigl( \tau^4 + (1 - \tau)^4 \bigr) - \frac{3\beta + 6}{24(7\beta + 18)} + \frac{1}{4} \tau^2 (1 - \tau)^2, $$

where $\tau \sim \mathrm{Beta}(\beta + 1, \beta + 1)$ and $Y_Q', Y_Q'' \sim \mathcal{Q}$, with $\tau, Y_Q', Y_Q''$ independent.

## Expansion

Dividing the recursion for $QIB$ by $n^4$ and centering gives $Y_n^Q = (L_n/n)^4 Y_{L_n}^Q + (1 - L_n/n)^4 Y_{n-L_n}^Q + C_n(L_n)$ with an explicit toll function $C_n$ that is a polynomial in $L_n$ and $n$ plus a vanishing remainder; as $L_n/n \to \tau$, $C_n(L_n) \to \frac{3\beta+6}{24(7\beta+18)}(\tau^4 + (1-\tau)^4 - 1) + \frac{1}{4}\tau^2(1-\tau)^2$, using $\binom{m}{4} \approx m^4/24$ and $\binom{L}{2}\binom{n-L}{2} \approx L^2 (n-L)^2 / 4$. Rösler's contraction method applies: the map sending a law $\mu$ to the law of the right-hand side is a contraction on the space of mean-zero, finite-variance laws under $d_2$, because $\mathbb{E}[\tau^8 + (1-\tau)^8] < 1$; a recursive inequality for $d_2(Y_n^Q, Y_Q)$ then forces it to $0$, once $\mathbb{E}(Y_n^Q)^2$ is shown to be uniformly bounded.

## Sources

- Krzysztof Bartoszek, "Limit distribution of the quartet balance index for Aldous’s $(\beta \ge 0)$-model", Applicationes Mathematicae 47 (2020), 29–44, <https://doi.org/10.4064/am2385-6-2019>. Published version of arXiv:1803.02136, cited next; locators there refer to the arXiv version.
- Krzysztof Bartoszek, "Limit distribution of the quartet balance index for Aldous's $(\beta \ge 0)$-model", arXiv (2018). Section 2 (quartet index and its recursion), Theorem 3.1 (contraction method), Theorem 4.1. <https://doi.org/10.48550/arXiv.1803.02136>
