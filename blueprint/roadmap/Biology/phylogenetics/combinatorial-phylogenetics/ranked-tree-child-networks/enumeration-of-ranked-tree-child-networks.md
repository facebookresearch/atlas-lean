# Enumeration of ranked tree-child networks

**Objects.** A *tree-child network* is a binary phylogenetic network (rooted DAG with tree vertices of in/out-degree $1/2$, reticulations of in/out-degree $2/1$, and leaves) in which every internal vertex has a child that is a tree vertex or a leaf. A *ranked tree-child network* (RTCN) on $\ell$ labeled leaves additionally orders its $\ell-1$ events $U_1 \prec \dots \prec U_{\ell-1}$ in time, each event being either a *branching* or a *reticulation event* (a branching whose new lineage is immediately merged into a contemporary lineage, so that $b + r = \ell - 1$). Its *profile* is $\mathbf q = (q_1,\dots,q_{\ell-1})$ with $q_k = 1$ if $U_k$ is a branching and $q_k = 0$ otherwise ($q_1 = 1$). A tree-child network is *temporal* if and only if it is the underlying network of some RTCN, and the fraction of tree-child networks that admit a ranking tends to $0$.

**Theorem (enumeration).** The number of RTCNs with profile $\mathbf q$ is

$$F(\mathbf q) = \prod_{k=1}^{\ell-1}\big(q_k + (k-1)(1-q_k)\big)\; T_\ell, \qquad T_\ell = \frac{\ell!\,(\ell-1)!}{2^{\ell-1}},$$

where $T_\ell$ is the number of ranked trees on $\ell$ labeled leaves. Hence the number with $b$ branchings is $C_{\ell,b} = {\ell-1 \brack b}\,T_\ell$ (unsigned Stirling numbers of the first kind), and the total number of RTCNs with $\ell \ge 2$ labeled leaves is

$$C_\ell = \frac{\ell!\,\big((\ell-1)!\big)^2}{2^{\ell-1}}.$$

**Uniform sampling (backward).** Start from $\ell$ labeled lineages; while $k+1 \ge 2$ lineages remain, choose uniformly among all $\binom{k+1}{2}$ coalescences of two lineages and all $(k-1)\binom{k+1}{2}$ reticulations of three lineages. The result is a uniform RTCN.

**Corollary (profile law).** The profile of a uniform RTCN is a vector of independent Bernoulli variables with $\mathbb P(q_k = 1) = 1/k$. The number of branchings $B_\ell$ is thus distributed as the number of cycles of a uniform permutation of $\{1,\dots,\ell-1\}$: $\mathbb E[B_\ell] = H_{\ell-1}$, $d_{\rm TV}(B_\ell,\mathrm{Poisson}(H_{\ell-1})) \to 0$, and $(B_\ell - \log\ell)/\sqrt{\log\ell} \Rightarrow \mathcal N(0,1)$.

## Expansion

Going back in time, the $k$-th event (counted from the root) acts on $k+1$ lineages: a branching corresponds to one of $\binom{k+1}{2}$ unordered pairs, a reticulation to choosing the pair that coalesces and one of the $k-1$ other lineages to absorb. Multiplying over events gives $F(\mathbf q)$; the factor $q_k + (k-1)(1-q_k)$ is exactly the weight of a Feller coupling, which is why the profile has the law of the cycle-indicator sequence of a uniform permutation and Stirling numbers appear.

## Sources

- François Bienvenu, Amaury Lambert and Mike Steel, "Combinatorial and stochastic properties of ranked tree-child networks", arXiv:2007.09701 (2020), Propositions 1.6 and 1.8, Theorem 2.3, Corollaries 2.4–2.5, Proposition 2.6 and Corollary 2.7, <https://doi.org/10.48550/arXiv.2007.09701>.
