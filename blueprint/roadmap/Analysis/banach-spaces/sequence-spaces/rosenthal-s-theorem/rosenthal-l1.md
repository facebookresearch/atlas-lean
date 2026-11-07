# Rosenthal's $\ell^1$ theorem

Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$ and let $(x_n)_{n \in \mathbb{N}}$ be a bounded sequence in $E$. Then there is a
strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$ such that either the subsequence
$(x_{\varphi(n)})_{n \in \mathbb{N}}$ is weakly Cauchy, that is, for every continuous linear
functional $f : E \to \mathbb{K}$ and every real $\varepsilon > 0$ there is $N$ with
$|f(x_{\varphi(m)}) - f(x_{\varphi(n)})| < \varepsilon$ for all $m, n \ge N$, or
$(x_{\varphi(n)})_{n \in \mathbb{N}}$ has a uniform $\ell^1$ lower bound.

Proof: We use the Nash-Williams/Galvin-Prikry Ramsey route, following Rosenthal's 1974 theorem,
Albiac and Kalton, Sections 10.1–10.2, and Farahat's 1974 proof.

## Sources

- H. P. Rosenthal, A Characterization of Banach Spaces Containing l1, PNAS 71 (1974), 2411–2413, DOI 10.1073/pnas.71.6.2411, ℓ¹ dichotomy theorem; Bourgain et al., extensions; Lean states `RCLike` Banach bounded `Set.range` dichotomy with `StrictMono φ` and `HasUniformL1LowerBound` defined via `ℕ →₀ 𝕜` finitely supported coefficients.
