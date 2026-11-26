# Leaf-height law of large numbers and CLT in the critical beta-splitting tree

**Model.** In the critical beta-splitting tree $\mathrm{CTCS}(n)$, a clade of $m \ge 2$ leaves splits into sub-clades of sizes $i$ and $m-i$ with probability

$$q(m,i) = \frac{m}{2h_{m-1}}\cdot\frac{1}{i(m-i)}, \qquad 1 \le i \le m-1,\qquad h_{m-1} = \sum_{j=1}^{m-1}\frac1j,$$

and in continuous time each clade of size $m$ waits an Exponential$(h_{m-1})$ time before splitting; clades of size $1$ are leaves. Let $D_n$ be the (continuous) height of a uniform random leaf and $L_n$ its height in number of edges. Following the path to the leaf, the clade sizes form the *harmonic descent chain*: a continuous-time Markov chain on $\{1,2,\ldots\}$ with jump rates $\lambda_{m,i} = 1/(m-i)$ for $1 \le i < m$, absorbed at $1$; $D_n$ is its absorption time from $n$ and $L_n$ is the number of jumps.

**Proposition (pairwise split time).** For every $n \ge 2$, the height of the branch point between the paths to two distinct uniform random leaves is exactly Exponential$(1)$.

**Theorem (heights).** As $n \to \infty$,

$$\frac{\mathbb{E}[D_n]}{\log n} \to \mu = \frac{1}{\zeta(2)} = \frac{6}{\pi^2}, \qquad \frac{D_n - \mu\log n}{\sqrt{\log n}} \xrightarrow{d} \mathrm{Normal}\Big(0, \frac{2\zeta(3)}{\zeta(2)^3}\Big),$$

$$\frac{\mathbb{E}[L_n]}{\log^2 n} \to \frac{1}{2\zeta(2)}, \qquad \frac{L_n - \frac{1}{2\zeta(2)}\log^2 n}{\log^{3/2} n} \xrightarrow{d} \mathrm{Normal}\Big(0, \frac{2\zeta(3)}{3\zeta(2)^3}\Big).$$

More precisely $\mathbb{E}[D_n] = \frac{6}{\pi^2}\log n + c_0 + O(1/n)$ with $c_0 = \frac{\zeta(3)}{\zeta(2)^2} + \frac{\gamma}{\zeta(2)}$ (Euler's constant $\gamma$), and $\operatorname{Var}(D_n) = \frac{2\zeta(3)}{\zeta(2)^3}\log n + O(1)$.

## Expansion

For large $m$, a jump of the harmonic descent chain from $m$ to $i$ changes $\log m$ by $a = \log(m/i)$ at rate approximately $f_\infty(a) = e^{-a}/(1-e^{-a})$, so $\log X_t \approx \log n - Y_t$ for a subordinator $Y$ with Lévy measure $\psi_\infty[a,\infty) = -\log(1-e^{-a})$. Its mean is $\int_0^\infty -\log(1-e^{-a})\,da = \zeta(2)$ and its variance rate is $2\zeta(3)$, so the renewal CLT for the first passage of $Y$ above $\log n$ gives mean $\log n/\zeta(2)$ and variance $\mu^3\cdot 2\zeta(3)\log n$. The edge count $L_n$ accumulates rate $h_{m-1} \approx \log m$ per unit time along the path, which integrates to $\tfrac12 \mu \log^2 n$.

## Sources

- David J. Aldous, Svante Janson, "The Critical Beta-splitting Random Tree II: Overview and Open Problems", arXiv:2303.02529 (2023), Proposition 1 and Theorems 2–6 (Section 2, "Heights and related statistics"); the theorems are proved in the companion papers it surveys, <https://doi.org/10.48550/arXiv.2303.02529>.
