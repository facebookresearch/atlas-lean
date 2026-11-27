# Symmetries of a selection process preserve transition probabilities

**Setting (selection process).** Let $G$ be a finite set of $n$ genetic sites, each holding allele $0$ or $1$; a state is $\mathbf x = (x_g)_{g \in G} \in \{0,1\}^G$. In each state $\mathbf x$, a parentage map $\alpha : G \to G$ and a mutation set $U \subseteq G$ are drawn with joint probability $p_{\mathbf x}(\alpha, U)$, and the next state is

$$x'_g = x_{\alpha(g)} \ \ (g \notin U), \qquad x'_g = 1 - x_{\alpha(g)} \ \ (g \in U).$$

The pair $(G, p)$ is a *selection process* if it satisfies the fixation axiom: some site $g$ and parentage maps $\alpha_1, \dots, \alpha_m$ with $p_{\mathbf x}(\alpha_k) > 0$ for all $k$ and all $\mathbf x$ satisfy $\alpha_1 \circ \cdots \circ \alpha_m(h) = g$ for every $h \in G$. Write $P_{\mathbf x \to \mathbf y}$ for the transition probabilities of the resulting selection Markov chain on $\{0,1\}^G$, and $(\mathbf x_\tau)_g = x_{\tau(g)}$ for a map $\tau : G \to G$.

**Definition.** A *symmetry* of $(G,p)$ is a permutation $\sigma$ of $G$ such that for every state $\mathbf x$, parentage map $\alpha$ and mutation set $U$,

$$p_{\mathbf x}(\alpha, U) = p_{\mathbf x_\sigma}\big(\sigma^{-1} \circ \alpha \circ \sigma,\ \sigma^{-1}(U)\big).$$

**Lemma.** The symmetries form a subgroup $\mathrm{Sym}(G,p)$ of the symmetric group on $G$.

**Theorem.** For every $\sigma \in \mathrm{Sym}(G,p)$ and all states $\mathbf x, \mathbf y$,

$$P_{\mathbf x \to \mathbf y} = P_{\mathbf x_\sigma \to \mathbf y_\sigma}.$$

**Consequence (equivalent sites).** Call sites $g \sim h$ if $\sigma(g) = h$ for some symmetry; the classes are the orbits of $\mathrm{Sym}(G,p)$ on $G$. Without mutation, the fixation probability $\rho_{\mathbf x} = \lim_{m\to\infty} P^{(m)}_{\mathbf x \to \mathbf 1}$ satisfies $\rho_{\mathbf x} = \rho_{\mathbf x_\sigma}$, so a single mutant has the same fixation probability at any two equivalent sites. If the action on $G$ is transitive (as for well-mixed haploid populations, or cycles and other vertex-transitive graphs), all sites are equivalent.

## Expansion

The transition $\mathbf x \to \mathbf y$ is the sum of $p_{\mathbf x}(\alpha, U)$ over pairs $(\alpha, U)$ producing $\mathbf y$. Conjugation $(\alpha, U) \mapsto (\sigma^{-1}\alpha\sigma, \sigma^{-1}(U))$ is a bijection of such pairs onto those taking $\mathbf x_\sigma$ to $\mathbf y_\sigma$: if $y_g = x_{\alpha(g)}$ (or its flip) then $(\mathbf y_\sigma)_g = y_{\sigma(g)} = x_{\alpha\sigma(g)} = (\mathbf x_\sigma)_{\sigma^{-1}\alpha\sigma(g)}$, and the mutated sites move to $\sigma^{-1}(U)$. The symmetry condition says the two sums agree term by term. The group property follows by composing the defining identity. For fixation, iterate the identity for $m$-step probabilities and use $\mathbf 1_\sigma = \mathbf 1$.

## Sources

- Benjamin Allen, "Symmetry in models of natural selection", *Journal of The Royal Society Interface* 20 (2023), 20230306, <https://doi.org/10.1098/rsif.2023.0306>. Numbering as in the preprint arXiv:2307.06495v1, <https://arxiv.org/abs/2307.06495v1>: Sections 2–4, the definition of symmetry, Theorem 1 and Lemma 1.
