# Monophyly numbers of phylogenetic trees

**Setting.** Let $T$ be a rooted phylogenetic tree with leaf set $X=\{1,\dots,n\}$, and for a vertex $v$ let $L(v)$ be its set of leaf descendants. A *character* is a map $f:X\to C$ to a set of $c=|C|$ traits. A vertex $v$ **induces monophyly** for $f$ if some trait $a\in C$ is carried by exactly the leaves in $L(v)$, that is, $f(\ell)=a\iff \ell\in L(v)$; it induces *relevant* monophyly if moreover $|L(v)|\ge2$. A character is *(relevant) monophyletic* if some vertex induces (relevant) monophyly for it, and *(relevant) fully monophyletic* if every leaf lies below such a vertex. The four counts over all $c^n$ characters are the relevant monophyly number $m(T,c)$, the monophyly number $m_N(T,c)$, and the full versions $fm(T,c)$, $fm_N(T,c)$. An *antichain* is a set $A$ of vertices no one of which is an ancestor of another; $s(A)=|\bigcup_{v\in A}L(v)|$, and $(c)_k=c(c-1)\cdots(c-k+1)$ is the falling factorial.

**Lemma (single vertex) and Corollary 3.** For any vertex $v$, the number of characters for which $v$ induces monophyly is $c\,(c-1)^{n-|L(v)|}$. The vertices inducing monophyly for a fixed character form an antichain.

**Theorem 4 (general formula).** With $\mathcal A$ the set of nonempty antichains of $T$,
$$m_N(T,c)=\sum_{A\in\mathcal A}(-1)^{|A|+1}\,(c)_{|A|}\,(c-|A|)^{\,n-s(A)},$$
with the convention $(c-|A|)^0=1$; the relevant number $m(T,c)$ is the same sum over antichains of internal vertices.

**Theorem 7 and Theorem 13 (tree shapes).** For the caterpillar $T^{cat}_n$ ($n\ge2$, $c\ge2$), $m(T^{cat}_n,c)=\sum_{j=0}^{n-2}c\,(c-1)^j$, and $fm(T^{cat}_n,c)=c$ independently of $n$ (Corollary 10). For the fully balanced tree of height $h$, $m_N$ and $fm$ are explicit finite sums over antichain-count coefficients, and $fm(T^{fb}_h,c)=fm_N(T^{fb}_{h-1},c)$ (Proposition 15).

**Theorem 19 (binary characters).** If $T=(T_1,T_2)$ is rooted binary with $n\ge2$ leaves and maximal pendant subtrees of sizes $n_1\ge n_2$, then $m(T,2)=2n-4$ if $n_2>1$ and $2n-2$ if $n_2=1$, and $m_N(T,2)=4n-4$. Consequently (Propositions 20 and 21),
$$\mathbb E_{\mathrm{unif}}[m(T_n,2)]=2n-3+\frac{3}{2n-3},\qquad \mathbb E_{\mathrm{Yule}}[m(T_n,2)]=2n-4+2\prod_{i=3}^{n-1}\frac{i-1}{i}.$$

## Expansion

Fixing $v$ and the trait $a$ on $L(v)$ forces all other leaves to avoid $a$, which gives the single-vertex count. Two comparable vertices cannot both induce monophyly, since the trait of the lower one would also have to appear outside it; distinct incomparable inducing vertices need distinct traits. Inclusion-exclusion over the events "$v$ induces monophyly" therefore runs over antichains $A$: choose distinct traits for the $|A|$ clades in $(c)_{|A|}$ ways and colour the remaining $n-s(A)$ leaves avoiding them. For two traits, $v$ induces monophyly exactly when $L(v)$ carries one trait and every other leaf the other, so each vertex and each choice of trait gives one character. A binary tree has $2n-1$ vertices, giving $2(2n-1)$ pairs, and the only coincidences are the two root children, which induce monophyly for the same two characters; hence $m_N(T,2)=4n-4$. Restricting to the $n-1$ internal vertices gives $2n-2$, reduced by $2$ when both root children are internal ($n_2>1$). Averaging the indicator of $n_2=1$ under the uniform and Yule models gives the expectations. Fully monophyletic characters are convex on $T$ (Proposition 22), connecting them to maximum parsimony.

## Sources

- M. Fischer, M. Hendriksen, K. Wicke, "Enumerating monophyletic characters in mathematical phylogenetics", arXiv preprint (2026), Corollary 3, Theorem 4, Theorem 7, Corollary 10, Theorem 13, Proposition 15, Theorem 19, Propositions 20-22, <https://doi.org/10.48550/arXiv.2607.22097>.
