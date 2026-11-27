# Robinson–Foulds distance via the LCA mapping

Let $S$ and $T$ be rooted trees with $\mathcal L(S) \subseteq \mathcal L(T)$. Write $I(\cdot)$ for the non-root internal nodes, $\mathcal C(u) = \mathcal L(S_u)$ for the cluster of node $u$, and $\mathcal H(\cdot)$ for the set of clusters of non-root internal nodes. The (unnormalized) **Robinson–Foulds distance** is

$$\mathrm{RF}(S, T) = \big|\mathcal H(S)\,\triangle\,\mathcal H(T[\mathcal L(S)])\big|,$$

with $T[\mathcal L(S)]$ the leaf-induced subtree. For a profile $\mathcal P = (T_1, \dots, T_k)$ and a binary supertree $T^*$ on $\bigcup_i \mathcal L(T_i)$, $\mathrm{RF}(\mathcal P, T^*) = \sum_i \mathrm{RF}(T_i, T^*)$; an **RF supertree** minimizes it.

The **LCA mapping** $\mathcal M_{S,T} : V(S) \to V(T)$ sends $u$ to $\mathrm{lca}_T(\mathcal C(u))$. Let $f_T(u) = 1$ if the cluster $\mathcal C(u)$ of $u \in I(S)$ is a cluster of $T$ and $0$ otherwise, and $\mathcal F_T = \{u \in I(S) : f_T(u) = 0\}$. Assume $\mathcal L(S) = \mathcal L(T)$ (otherwise restrict $T$ first).

**Lemma 1.** $\mathrm{RF}(S, T) = |I(T)| - |I(S)| + 2\,|\mathcal F_T|$.

**Lemma 2.** For $u \in I(S)$, $f_T(u) = 1$ if and only if $|\mathcal C(u)| = |\mathcal L(T_{\mathcal M_{S,T}(u)})|$.

Consequently $\mathrm{RF}(S, T)$ is computable in $O(n)$ time from the LCA mapping, and minimizing $\mathrm{RF}$ over trees with a fixed node count reduces to minimizing $|\mathcal F_T|$.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Lemma 1 is counting: shared clusters number $|I(S)| - |\mathcal F_T|$, and the symmetric difference is $|I(T)| + |I(S)| - 2(|I(S)| - |\mathcal F_T|)$. For Lemma 2, $\mathcal C(u) \subseteq \mathcal L(T_{\mathcal M(u)})$ always, with equality exactly when the cluster appears in $T$; a bottom-up pass gives the LCA mapping and the leaf counts in linear time.

## Sources

- M. S. Bansal, J. G. Burleigh, O. Eulenstein, D. Fernández-Baca, "Robinson-Foulds supertrees", Algorithms for Molecular Biology 5 (2010) 18, Definitions 1 and 6, Lemmas 1–2, <https://doi.org/10.1186/1748-7188-5-18>, PMCID PMC2846952.
