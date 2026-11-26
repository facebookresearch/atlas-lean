# Bessel-number counts of unlabeled spinal tree-child networks

**Setting.** A binary phylogenetic network is a rooted DAG whose vertices are a root (outdegree 1), leaves, tree vertices (in 1, out 2) and reticulations (in 2, out 1); it is *tree-child* if every non-leaf vertex has a child that is not a reticulation. A tree-child network is *spinal* if all its internal vertices lie on a single directed path from the root, the *spine*. Let $\mathcal{STC}_{n,k}$ be the binary spinal tree-child networks on leaves $[n]$ with $k$ reticulations, $\mathcal{NLSTC}_{n,k}$ their unlabeled versions (leaf labels forgotten), and $\mathcal{NLSCTC}_{n,k}$ the unlabeled *spinal caterpillar* tree-child networks, where each leaf whose sibling is a reticulation may be replaced by a caterpillar.

**Words.** Following Pons and Batle, $\mathcal{C}_{n,k}$ is the class of words of length $2n+k$ over $a_1,\dots,a_n$ in which $a_1,\dots,a_k$ occur three times and $a_{k+1},\dots,a_n$ twice, and every prefix $z$ satisfies $\#(z,a_i) = 0$ or $\#(z,a_i) \ge \#(z,a_j)$ for all $j \ge i$. Let $C^1_{n,k} \subset \mathcal{C}_{n,k}$ consist of the words ending with $a_{k+1}a_{k+2}\cdots a_n$ in which, for every $i \le k$, the second and third occurrences of $a_i$ are adjacent, and let $\sim$ identify words that differ by permuting the first occurrences of $a_{k+1},\dots,a_n$.

**Lemma.** A network in $\mathcal{NLSTC}_{n,k}$ has $t = n+k-1$ tree vertices and a spine of length $n+2k$.

**Theorem.** There is a bijection $\mathcal{NLSTC}_{n,k} \leftrightarrow C^1_{n-1,k}/{\sim}$, and

$$|C^1_{n,k}/{\sim}| = \frac{(n+k)!}{2^k\,(n-k)!\,k!} \quad (k \le n), \qquad\text{so}\qquad |\mathcal{NLSTC}_{n,k}| = \frac{(n-1+k)!}{2^k\,(n-1-k)!\,k!} \quad (k \le n-1),$$

a coefficient of the Bessel polynomials (the number of partitions of an $(n-1+k)$-set into $n-1-k$ singletons and $k$ pairs). For spinal caterpillar networks there is a bijection with a second word class $C^2_{n-1,k}/{\sim}$, and

$$|\mathcal{NLSCTC}_{n,k}| = \binom{n-1+2k}{n-1-k}\,\frac{(2k)!}{2^k\,k!} \qquad (k \le n-1).$$

**Generating-function route.** Removing the spine end yields marked trees: $|\mathcal{STC}_{n,k}| = \frac{n}{2}|\mathcal{MT}_{n-1,k+1}| + n(n+k-2)|\mathcal{MT}_{n-1,k}|$ and $|\mathcal{NLSTC}_{n,k}| = |\mathcal{NLMT}_{n-1,k+1}| + (n+k-2)|\mathcal{NLMT}_{n-1,k}|$, where the marked-tree classes satisfy the boxed-product specification $\mathcal{MT} = \mathcal{R} \boxprod (\mathrm{Seq}(\mathcal{MT} \sqcup \mathcal{L}) \star \mathcal{L})$. Extracting coefficients recovers, for $n > 1$,

$$|\mathcal{STC}_{n,k}| = \frac{n!\,(n+k-2)!\,(n+3k-1)}{2^{k+1}\,k!\,(n-k-1)!}, \qquad |\mathcal{NLSTC}_{n,k}| = \frac{(n+k-1)!}{2^k\,k!\,(n-k-1)!}.$$

## Expansion

The edge count $1 + 2t + k = t + 2k + n$ gives $t = n+k-1$, and the spine visits all $t + k$ internal vertices. Reading the spine from the root, each tree vertex either hangs a leaf or is the upper parent of a reticulation, and each reticulation has its lower parent further down; recording the vertices as letters (three occurrences per reticulation, two per hanging leaf) produces a word in $C^1_{n-1,k}$, and forgetting leaf labels corresponds to the quotient by $\sim$. Counting the words reduces to placing $k$ adjacent pairs among the remaining letters, which gives the Bessel numbers. The words realize the spinal case of the Pons–Batle conjecture $|\mathcal{TC}_{n,k}| = \frac{n!}{(n-k)!}|\mathcal{C}_{n-1,k}|$ relating all tree-child networks to $\mathcal{C}_{n-1,k}$.

## Sources

- Pau Vives, Anna de Mier, Gabriel Cardona and Joan Carles Pons, "Counting spinal tree-child networks via word encodings and generating functions", arXiv:2605.10926 (2026), Section 2 (Conjecture 1, Theorem 3), Section 3 (Lemma 4, Propositions 5–6, Corollary 7, Propositions 8–9, Corollary 10) and Section 4 (Propositions 11–18), <https://doi.org/10.48550/arXiv.2605.10926>.
