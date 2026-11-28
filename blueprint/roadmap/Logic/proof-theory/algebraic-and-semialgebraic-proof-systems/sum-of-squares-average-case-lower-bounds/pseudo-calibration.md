# Pseudo-calibration

Pseudo-calibration builds a candidate Sum-of-Squares pseudo-expectation $\tilde{\mathbb{E}}_G$ for a random graph $G$ by matching, on simple low-degree tests $f(G, x)$, its average over $G(n, 1/2)$ with the expectation under a planted distribution; for planted clique this fixes the low-degree Fourier coefficients of $G \mapsto \tilde{\mathbb{E}}_G$.

Let $G(n, 1/2)$ be the Erdős-Rényi distribution and $G(n, 1/2, \omega)$ the planted distribution of pairs $(G, x)$ obtained as follows: sample $G_0 \sim G(n, 1/2)$, put each vertex into a set $K \subseteq [n]$ independently with probability $\omega/n$, let $G$ be $G_0$ with all edges inside $K$ added, and let $x \in \{0,1\}^n$ be the indicator of $K$. The planted clique $K$ has *expected* size $\omega$; it is this independent-inclusion law that gives the moments $(\omega/n)^{|V(T) \cup S|}$ below (a clique of size exactly $\omega$ gives different moments, e.g. $\omega(\omega - 1)/(n(n-1))$ for $\mathbb{E}[x_i x_j]$). The informal **pseudo-calibration** desideratum for a family of linear maps $p \mapsto \tilde{\mathbb{E}}_G\, p$ on polynomials of degree at most $d$ in $x$ is

$$
\mathbb{E}_{G \sim G(n,1/2)} \, \tilde{\mathbb{E}}_G\, f_G = \mathbb{E}_{(G,x) \sim G(n,1/2,\omega)} \, f_G(x)
$$

for every simple function $f = f(G, x)$, i.e. every $f$ that is a low-degree polynomial both in the entries of the adjacency matrix of $G$ and in $x$. What "low degree" means is fixed by the truncation in the construction below, which attains the equation only for the test terms it retains.

**The pseudo-calibrated planted clique moments.** Encode $G$ by $g_e \in \{\pm 1\}$ for $e \in \binom{[n]}{2}$ and let $\chi_T = \prod_{e \in T} g_e$ for $T \subseteq \binom{[n]}{2}$, with $V(T)$ the set of vertices touched by $T$. For degree $d$, clique size $\omega$ and truncation $\tau$, define for each $S \subseteq [n]$ with $|S| \le d$

$$
\widehat{\tilde{\mathbb{E}}[x_S]}(T) = \mathbb{E}_{(G,x) \sim G(n,1/2,\omega)} [\chi_T(G) \, x_S] \quad \text{if } |V(T) \cup S| \le \tau, \qquad \text{and } 0 \text{ otherwise},
$$

and $\tilde{\mathbb{E}}[x_S] = \sum_{T} \widehat{\tilde{\mathbb{E}}[x_S]}(T) \, \chi_T(G)$, extended linearly to all multilinear polynomials of degree at most $d$. Here $\widehat{\tilde{\mathbb{E}}[x_S]}(T)$ is the normalized Fourier coefficient of $G \mapsto \tilde{\mathbb{E}}_G[x_S]$ on the cube $\{\pm 1\}^{\binom{[n]}{2}}$, and for retained $T$ (those with $|V(T) \cup S| \le \tau$) the planted law above gives the value $(\omega/n)^{|V(T) \cup S|}$.

**Exact fooling.** Write a test as $f_G(x) = \sum_S c_S(G) \, x_S$ with $c_S(G) = \sum_T \widehat{c_S}(T) \, \chi_T(G)$, so that $f$ is a combination of test terms $x_S \chi_T$. If every test term with $\widehat{c_S}(T) \ne 0$ satisfies $|S| \le d$ and the vertex cutoff $|V(T) \cup S| \le \tau$, then

$$
\mathbb{E}_{G \sim G(n,1/2)} \, \tilde{\mathbb{E}}_G\, f_G = \mathbb{E}_{(G,x) \sim G(n,1/2,\omega)} \, f_G(x) .
$$

The cutoff counts vertices, not edges: for $S = \emptyset$ and $T$ a matching of $\lfloor \tau/2 \rfloor + 1$ edges, the test $\chi_T$ has edge degree at most $\tau$ but touches more than $\tau$ vertices; its pseudo-calibrated average is $0$, while its planted expectation $(\omega/n)^{|V(T)|}$ is positive.

## Proof sketch

The motivation is Bayesian: a computationally bounded party cannot tell $G(n, 1/2)$ from the planted model, so its best-effort estimates of conditional expectations should be calibrated against the planted distribution on simple tests. The informal desideratum implies that every simple strong constraint (a function vanishing on all planted cliques) has pseudo-expectation $0$, and also many weak constraints, for example that a high-degree vertex is more likely to be in the clique. Earlier planted clique pseudo-expectations satisfied the strong constraints but violate such weak ones already at degree four, while for random 3-XOR pseudo-calibration reproduces Grigoriev's construction. Exact fooling follows by expanding $c_S$ in the Fourier basis and using orthogonality of the characters $\chi_T$; the truncated operator attains the desideratum exactly only for the retained terms. In the regime $\omega = n^{1/2 - \epsilon}$ with $\epsilon \in (0, 1/2)$, $\epsilon \ge C \log\log n / \log n$ and $C d/\epsilon \le \tau \le (\epsilon/C) \log n$ for a sufficiently large constant $C$, with high probability $\tilde{\mathbb{E}}[1] = 1 \pm n^{-\Omega(\epsilon)}$ and $\tilde{\mathbb{E}}[\sum_i x_i] = \omega (1 \pm n^{-\Omega(\epsilon)})$; and always $\tilde{\mathbb{E}}[x_S] = 0$ whenever $S$ is not a clique of $G$. Positivity of the moment matrix is the hard part and is proved by an approximate factorization over ribbons and graphical matrices.

## Depends on

- [Planted clique model, search and detection problems](../../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)
- [Fourier coefficient on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

None.

## Sources

- Boaz Barak, Samuel B. Hopkins, Jonathan A. Kelner, Pravesh K. Kothari, Ankur Moitra, Aaron Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", *SIAM Journal on Computing* 48(2), 2019, https://doi.org/10.1137/17M1138236; numbering of arXiv:1604.03084v2 (Section 2.1, the pseudo-calibration equation; Section 5 with its parameter box; Definition 5.1, the vertex cutoff; Lemma 5.2, the moments $(\omega/n)^{|V(T) \cup S|}$ of the independent-inclusion planted law; Lemma 5.3, whose printed edge-degree hypothesis is narrowed here to the vertex cutoff that its proof in Appendix A.1 uses; Lemmas 5.4 and 5.5; Sections 6 and 7).
