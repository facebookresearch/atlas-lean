# Pseudocalibration of pseudo-expectations

Let $\nu$ be a null distribution (e.g. $G(n, 1/2)$) and $\mu$ a planted distribution on pairs $(G, x)$ where $x$ is a hidden solution (e.g. the indicator of a planted clique). For a truncation degree $\tau$ and SoS degree $d$, the **pseudocalibrated candidate** assigns to every input $G$ and every monomial $x^{S}$, $|S| \le d$, the value

$$
\tilde{\mathbb{E}}_G[x^S] = \sum_{T \in \mathcal{T}_S} \mathbb{E}_{(G', x) \sim \mu}\bigl[x^{S} \chi_T(G')\bigr]\, \chi_T(G),
$$

where $\chi_T$ are the Fourier characters of $\nu$ and $\mathcal{T}_S$ is a truncation set of characters: $\{T : |T| \le \tau\}$ in the generic form, while for planted clique (Hopkins, Definition 11.3.1; Barak et al., Definition 5.1) $\mathcal{T}_S = \{T \subseteq \binom{[n]}{2} : |V(T) \cup S| \le \tau\}$, with $V(T)$ the set of vertices incident to $T$, which gives $\tilde{\mathbb{E}}_G[x^S] = \sum_{|V(T) \cup S| \le \tau} (k/n)^{|V(T) \cup S|} \chi_T(G)$ when each vertex joins the clique independently with probability $k/n$. Thus $\tilde{\mathbb{E}}_G[x^S]$ is the projection onto $\mathrm{span}\{\chi_T : T \in \mathcal{T}_S\}$ of $G \mapsto \frac{d\mu}{d\nu}(G)\, \mathbb{E}_{\mu}[x^S \mid G]$, the likelihood ratio of the graph times the posterior moment, not the posterior moment itself. In particular $\tilde{\mathbb{E}}_G[1]$, the case $S = \emptyset$, is a low-degree projection of the likelihood ratio and is not identically $1$, so the candidate is unnormalized: it must still be normalized and shown to be positive before it is a pseudo-expectation. It satisfies $\mathbb{E}_{G \sim \nu}\big[\tilde{\mathbb{E}}_G[x^S]\, f(G)\big] = \mathbb{E}_{(G,x) \sim \mu}[x^S f(G)]$ for every function $f$ of the graph in $\mathrm{span}\{\chi_T : T \in \mathcal{T}_S\}$.

## Depends on

- [The degree-d SoS relaxation of the clique number](planted-clique-sos-value.md)

## Sources

- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
- S. B. Hopkins, "Statistical inference and the sum of squares method", PhD thesis, Cornell University (2018).
