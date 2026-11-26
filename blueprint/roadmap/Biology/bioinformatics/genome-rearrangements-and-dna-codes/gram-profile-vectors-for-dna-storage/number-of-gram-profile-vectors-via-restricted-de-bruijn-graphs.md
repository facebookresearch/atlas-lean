# Number of $\ell$-gram profile vectors via restricted de Bruijn graphs

**Setting.** For a word $x \in \{0,\dots,q-1\}^n$ and $\ell < n$, the **$\ell$-gram profile vector** $p(x;q,\ell)$ is indexed by the $q^\ell$ words of length $\ell$ and records how often each occurs as a substring of $x$; its entries sum to $n-\ell+1$. In DNA-based data storage, synthesized strands are fragmented and sequenced, so the reader observes (a noisy version of) the profile rather than the word. Fix a set $S \subseteq \{0,\dots,q-1\}^\ell$ of allowed $\ell$-grams (for example, a GC-content constraint) and let $p(x;S)$ be the profile restricted to $S$ for words all of whose $\ell$-grams lie in $S$. Words with equal profiles are indistinguishable; let $\mathcal{Q}(n;S)$ be the set of these equivalence classes and $\mathbf{p}\mathcal{Q}(n;S)$ the set of attainable profile vectors, so $|\mathbf{p}\mathcal{Q}(n;S)| = |\mathcal{Q}(n;S)|$.

The **restricted de Bruijn graph** $D(S)$ has as nodes $V(S)$ the $(\ell-1)$-grams occurring in words of $S$, and an arc from $v_1\cdots v_{\ell-1}$ to $v_2\cdots v_\ell$ for each $v_1\cdots v_\ell \in S$, so arcs are identified with $S$. Let $B$ be its node–arc incidence matrix (loops give zero columns), $A(S)$ the matrix $B$ with an all-ones row on top, and $b = (1,0,\dots,0)^T$. Define the integer-point sets

$$\mathcal{F}(n;S) = \{u \in \mathbb{Z}^{|S|} : A(S)u = (n-\ell+1)b,\ u \ge 0\}, \qquad \mathcal{E}(n;S) = \{u \in \mathbb{Z}^{|S|} : A(S)u = (n-\ell+1)b,\ u > 0\}.$$

Let $\bar{\mathcal{Q}}(n;S)$ be the classes of **closed** words (first and last $(\ell-1)$-grams equal) and $\mathbf{p}\bar{\mathcal{Q}}(n;S)$ their profiles. Write $f(n) = \Theta'(g(n))$ if $f = O(g)$ and there are an integer $\lambda$ and $c > 0$ with $f(n) \ge c\,g(n)$ for all large $n$ with $\lambda \mid (n-\ell+1)$.

**Lemma (Eulerian realization).** If $D(S)$ is strongly connected, then $\mathcal{E}(n;S) \subseteq \mathbf{p}\bar{\mathcal{Q}}(n;S) \subseteq \mathcal{F}(n;S)$.

**Theorem.** Suppose $D(S)$ is strongly connected and let $\lambda$ be the least common multiple of the lengths of all cycles of $D(S)$. Then $|\mathcal{E}(n;S)|$ and $|\mathcal{F}(n;S)|$ are quasipolynomials in $n$ of the same degree $|S| - |V(S)|$, with a common period dividing $\lambda$. Consequently

$$|\mathbf{p}\bar{\mathcal{Q}}(n;S)| = \Theta'\big(n^{|S|-|V(S)|}\big), \qquad |\mathbf{p}\mathcal{Q}(n;S)| = \Theta'\big(n^{|S|-|V(S)|}\big),$$

and the same order holds for profiles of words with prescribed first and/or last $(\ell-1)$-gram. For the unrestricted alphabet $S = \{0,\dots,q-1\}^\ell$ this gives order $n^{q^\ell - q^{\ell-1}}$, matching the asymptotic count of Jacquet et al.

## Expansion

A profile of a closed word is a circulation on $D(S)$: flow conservation $Bu = 0$ holds and the total flow is $n-\ell+1$, so it lies in $\mathcal{F}(n;S)$. Conversely, a strictly positive integer circulation defines an Eulerian multidigraph (strong connectivity plus balanced degrees), and an Euler tour spells a closed word with that profile, so $\mathcal{E}(n;S)$ is realized. Both sets are the lattice points of the $(n-\ell+1)$-th dilate of the rational polytope $\{u \ge 0 : A(S)u = b\}$ (respectively its relative interior), whose dimension is $|S| - \operatorname{rank}A(S) = |S| - |V(S)|$ since $B$ has rank $|V(S)|-1$ for a connected graph. Ehrhart's theorem makes the counts quasipolynomials whose period divides the lcm of vertex denominators; the polytope's vertices are normalized cycle indicator vectors, so denominators are cycle lengths. Ehrhart–Macdonald reciprocity relates the interior count to the closed count, giving the same degree. The number of distinguishable codewords therefore grows only polynomially in $n$, which bounds the rate of $\ell$-gram reconstruction codes for DNA storage.

## Sources

- Han Mao Kiah, Gregory J. Puleo and Olgica Milenkovic, "Codes for DNA Sequence Profiles", arXiv:1502.00517 (2015), Section 3: Lemma 3.2, Theorem 3.3 and Corollary 3.4; proof via Ehrhart theory in Section 4, <https://doi.org/10.48550/arXiv.1502.00517>. Published version: 2015 IEEE International Symposium on Information Theory (ISIT) (2015) 814–818, <https://doi.org/10.1109/isit.2015.7282568>.
