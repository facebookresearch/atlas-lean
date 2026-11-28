# Asymptotic count of normal and hybridization networks via tree decoration

**Definitions.** A rooted binary phylogenetic network on leaf set $[n] = \{1,\dots,n\}$ is a rooted acyclic digraph whose non-root, non-leaf vertices are tree vertices (in-degree 1, out-degree 2) or reticulation vertices (in-degree 2, out-degree 1). It is **tree-child** if every non-leaf vertex has a child that is a tree vertex or leaf, and **normal** if it is tree-child and has no shortcut (no arc $(u,v)$ with another directed path from $u$ to $v$). A **hybridization network** is a tree-child network with a temporal ranking: dates with $T(u) < T(v)$ on tree arcs and $T(u) = T(v) = T(w)$ for a reticulation $v$ with parents $u, w$. Every hybridization network is normal. Let $N_{n,k}$ and $H_{n,k}$ count normal and hybridization networks with $n$ leaves and $k$ reticulations, and $r_n = (2n-3)!!$ the number of rooted binary trees on $[n]$.

**Tree decoration.** A $k$-fold decorated tree places, one at a time, $k$ new arcs $(p_i, p'_i)$ between subdivision points of the edges of a rooted binary tree $T$ (with a root edge). For a fixed base tree there are

$$|S(T,k)| = \frac{(2n-1)(2n)\cdots(2n+2k-2)}{k!} \sim \frac{4^k n^{2k}}{k!}$$

such decorations, so in total $|S(n,k)| = r_n\,|S(T,k)| \sim \frac{2^{2k-1}\sqrt2}{k!}\big(\tfrac{2}{e}\big)^n n^{n+2k-1}$.

**Theorem.**
1. For fixed $k$, the fraction of $k$-fold decorated trees whose resulting digraph is not a normal network tends to $0$ as $n \to \infty$; the exceptions (cycles, non-tree-child or shortcut configurations) number $O\big((2/e)^n n^{n+2k-3/2}\big)$.
2. Consequently, since a normal network with $k$ reticulations displays exactly $2^k$ trees,

$$N_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}\Big(\frac{2}{e}\Big)^n n^{n+2k-1},$$

and this remains valid when $k = o(n^{1/3})$.
3. Hybridization networks have the same asymptotics: $H_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}(2/e)^n n^{n+2k-1}$ for fixed $k$, and also for $k = o(n^{1/3})$.

## Expansion

Each normal network with $k$ reticulations arises from exactly $2^k$ (tree, decoration) pairs, one for each displayed tree, so counting normal networks reduces to counting decorations that produce them. Bad decorations are controlled through the induced subdivision tree spanned by the $2k$ attachment points: decorations whose induced tree has $\ell$ internal subdivision vertices are counted with exponential generating functions in $r(z) = 1 - \sqrt{1-2z}$, and singularity analysis at $z = 1/2$ shows they contribute $O\big((2/e)^n n^{n+2k-1-\ell/2}\big)$; cycles and violations of normality all force $\ell \ge 1$ or comparable savings. Making the $k$-dependence explicit extends the result to $k = o(n^{1/3})$. For hybridization networks, a further estimate (Proposition 11) shows that normal decorations admitting no temporal ranking are also of lower order. Exact small cases include $H_{n,1} = N_{n,1}$, $H_{4,1} = 54$, and $H_{4,2} = 36$ against $N_{4,2} = 48$.

## Sources

- M. Fuchs, M. Steel, Q. Zhang, "Asymptotic enumeration of normal and hybridization networks via tree decoration", Bulletin of Mathematical Biology (2025), Lemma 1 and Eq (1), Lemmas 3–4, Propositions 5–6, Corollary 7 (Eq 5), Remark 2, Eq (14) and Theorem 12 (Eq 15), <https://doi.org/10.1007/s11538-025-01444-y>, PMCID PMC12058904.
