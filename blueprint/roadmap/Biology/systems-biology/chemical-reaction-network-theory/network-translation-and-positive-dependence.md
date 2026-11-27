# Network translation and positive dependence of reaction vectors

Let $\mathscr{N}$ be a chemical reaction network on $m$ species with reaction set $\mathscr{R}$, stoichiometric matrix $N$ (columns $y'-y$ for $q\colon y \to y'$) and stoichiometric subspace $S = \operatorname{im} N \subseteq \mathbb{R}^m$, and let $K$ be a kinetics on it (each $K_q\colon \mathbb{R}^m_{\ge 0} \to \mathbb{R}_{\ge 0}$, positive where the reactant support is present).

**Network translation.** A kinetic system $(\tilde{\mathscr{N}},\tilde K)$ on the same species is a *translation* of $(\mathscr{N},K)$ if, for every $\zeta \in \mathbb{Z}^m$ and every $x \in \mathbb{R}^m_{\ge 0}$,

$$\sum_{q\colon y'-y=\zeta} K_q(x) = \sum_{\tilde q\colon z'-z=\zeta} \tilde K_{\tilde q}(x).$$

Translations are exactly the systems reachable by finitely many *shifts* ($y \to y'$ replaced by $y+z \to y'+z$, same kinetics), *divisions* (one reaction split into two shifted copies whose kinetics sum to the original) and *merges* (reactions with the same reaction vector combined, kinetics added). A translation has the same set of reaction vectors and the same stoichiometric subspace, and it is dynamically equivalent: $NK(x) = \tilde N \tilde K(x)$ for all $x$.

**Positive dependence.** $\mathscr{N}$ is *positively dependent* if there are $k_q > 0$ with $\sum_{q} k_q (y'_q - y_q) = 0$. The *stoichiometric cone* is $S_+ = \{\sum_q \alpha_q (y'_q - y_q) : \alpha_q \ge 0\} \subseteq S$.

**Theorem.** For a mass-action kinetic system $(\mathscr{N},K)$ the following are equivalent:

1. $\mathscr{N}$ is positively dependent;
2. $\ker N$ contains a vector with all entries positive;
3. $S_+ = S$;
4. for some choice of positive rate constants the system has a positive equilibrium, $E_+(\mathscr{N},K) \ne \emptyset$;
5. $(\mathscr{N},K)$ has a weakly reversible network translate.

In particular every weakly reversible network is positively dependent, and for an independent decomposition $\mathscr{N} = \mathscr{N}_1 \cup \dots \cup \mathscr{N}_k$ (stoichiometric subspaces forming a direct sum) $\mathscr{N}$ is positively dependent if and only if every $\mathscr{N}_i$ is.

## Depends on

- [Weak reversibility is equivalent to strongly connected linkage classes](../complex-balancing-and-the-deficiency-zero-theore/is-weakly-reversible-iff-reachable.md)

## Expansion

(1) and (2) are the same statement read through $N(a) = \sum_q a_q (y'_q - y_q)$. (2) gives (3): any $\gamma \in S$ is $N b$ for some $b$, and adding a large multiple of a positive kernel vector makes the coefficients nonnegative. For (4), a positive kernel vector $v$ and any $x^* > 0$ give rate constants $k_q = v_q / (x^*)^{y_q}$ making $x^*$ an equilibrium; conversely the rate vector at a positive equilibrium is a positive kernel vector. For (5), weakly reversible translates exist exactly when the reaction vectors can be rearranged into cycles, which is again a positivity condition on $\ker N$. The value of a weakly reversible translate is that deficiency-zero and complex-balancing results can then be applied to the translate, whose dynamics coincide with the original ones.

## Sources

- Dylan Antonio Talabis, Eduardo Mendoza, "Network transformation-based analysis of biochemical systems", *Journal of Mathematical Biology* 89(6) (2024), 62, Definitions 1 and 3, Propositions 1-3, Corollaries 1-3 and Theorem 1, <https://doi.org/10.1007/s00285-024-02152-2> (preprint arXiv:2308.12586).
