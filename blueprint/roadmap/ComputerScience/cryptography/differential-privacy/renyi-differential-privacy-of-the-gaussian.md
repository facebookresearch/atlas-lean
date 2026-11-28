# Rényi differential privacy of the Gaussian mechanism

Let $\mathrm{Adj}$ be a neighbouring relation on a set $X$ of databases, and let a real-valued query
$f : X \to \mathbb{R}$ satisfy $|f(x) - f(y)| \le \Delta$ whenever $\mathrm{Adj}(x, y)$. For a
variance $v > 0$, the *Gaussian mechanism* releases $f(x) + Z$ with $Z \sim \mathcal{N}(0, v)$, so
its output on $x$ has law $\mathcal{N}(f(x), v)$. For every order $\alpha > 1$ it is
$(\alpha, \alpha \Delta^2 / (2v))$-[Rényi differentially private](../renyi-differential-privacy/renyi-differential-privacy.md):

$$
D_\alpha\left(\mathcal{N}(f(x), v) \,\|\, \mathcal{N}(f(y), v)\right) \le \frac{\alpha \Delta^2}{2v} \quad \text{whenever } \mathrm{Adj}(x, y).
$$

For probability laws $P$ and $Q$, $D_\alpha(P \,\|\, Q) = \frac{1}{\alpha - 1} \log \int (dP/dQ)^\alpha \, dQ$
is the [Rényi divergence](../../../InformationTheory/information-inequalities/r-nyi-divergence/renyi-div.md)
when $P$ is absolutely continuous with respect to $Q$, and is $\infty$ otherwise. The logarithm is
natural. For the nondegenerate Gaussian laws here, the Radon–Nikodym derivative $dP/dQ$ is the
ratio of their densities.

With sensitivity $\Delta = 1$ and variance $v = \sigma^2$ this is Mironov's Corollary 3 at orders
$\alpha > 1$: the Gaussian mechanism is $(\alpha, \alpha / (2\sigma^2))$-Rényi differentially
private for every $\alpha > 1$. The statement here allows any bound $\Delta$ and any neighbouring
relation.

## Proof

For neighbours $x$ and $y$, apply the [Gaussian Rényi bound](../../../InformationTheory/information-inequalities/r-nyi-divergence/renyi-div-gaussian-real-le.md)
to the means $f(x)$ and $f(y)$, which satisfy $|f(x) - f(y)| \le \Delta$. It follows from the
[closed form](../../../InformationTheory/information-inequalities/r-nyi-divergence/renyi-div-gaussian-real.md)
$D_\alpha(\mathcal{N}(m, v) \,\|\, \mathcal{N}(n, v)) = \alpha (m - n)^2 / (2v)$ (Mironov's
Proposition 7 when $m = 0$), since $(m - n)^2 \le \Delta^2$.

## Sources

- I. Mironov, "Rényi differential privacy", *2017 IEEE 30th Computer Security Foundations Symposium (CSF)*, 263–275, <https://doi.org/10.1109/CSF.2017.11>; numbering of arXiv:1702.07476v3, <https://arxiv.org/abs/1702.07476v3>: Definition 3 (Rényi divergence), Definition 4 ($(\alpha, \varepsilon)$-Rényi differential privacy), Proposition 7 with its proof, and Corollary 3 (Section VI.C).
