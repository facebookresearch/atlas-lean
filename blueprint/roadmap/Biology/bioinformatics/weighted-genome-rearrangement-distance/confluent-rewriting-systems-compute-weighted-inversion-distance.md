# Confluent rewriting systems compute weighted inversion distance

**Setting.** A circular or linear chromosome with $n$ regions is a permutation $\pi$ of positions. Rearrangements are permutations of positions, composed from left to right; for example the inversion $t_{i,j} = (i,j)(i+1,j-1)\cdots$ reverses positions $i$ through $j$. A **weighted inversion system** $(G, S, \omega)$ consists of a set $S$ of allowed rearrangements, closed under inverses, that generates a group $G$, and positive weights $\omega : S \to \mathbb{R}_{>0}$, for example penalizing long inversions. The **weighted length** of $g\in G$ is

$$\ell_{S,\omega}(g) = \inf\Big\{\sum_{i=1}^t\omega(s_i) : s_1s_2\cdots s_t = g,\ s_i\in S\Big\},$$

and the weighted rearrangement distance between genomes $\pi_1, \pi_2$ is $\ell_{S,\omega}(\pi_2\pi_1^{-1})$.

**Weighted lexicographic order.** Fix a total order $\succ$ on $S$. For words $u = s_1\cdots s_k$ and $v = t_1\cdots t_l$, let $u > v$ if $\sum\omega(s_i) > \sum\omega(t_i)$, or if the weights are equal and $s_p \succ t_p$ at the first position $p$ where they differ.

**Proposition.** For finite $S$, the weighted lexicographic order is a reduction order on $S^*$: it is total, compatible with concatenation ($s > t \Rightarrow asb > atb$), and well-founded. Hence any rewriting system whose rules $l \to r$ satisfy $l > r$ terminates.

**Critical-pair lemma.** A terminating rewriting system is confluent if and only if all its critical pairs resolve, that is, all overlaps of rule left-hand sides rewrite to a common word.

**Consequence (path deformation).** Orient the relations of a presentation $\langle S\mid\mathcal{R}\rangle$ of $G$ by the weighted lexicographic order. If Knuth–Bendix completion terminates, it produces a finite confluent, terminating rewriting system. Every word for $g$ then reduces to the same irreducible normal form, which is the order-minimal word representing $g$. Because the order compares total weight first, this normal form has total weight $\ell_{S,\omega}(g)$. Thus rewriting any rearrangement path between two genomes, for example a sorting path from a standard algorithm, yields a minimum-weight path and hence the weighted distance.

## Expansion

Termination: every generator weighs at least $\min_S\omega > 0$, so only finitely many words have weight below any given bound, and no infinite strictly decreasing chain exists. Confluence plus termination gives a unique normal form in each equivalence class of $S^*$ modulo the relations, which is the set of words representing a fixed $g$. Every non-minimal word in a class is reducible, since otherwise there would be two distinct irreducible words in one class. So the normal form is the order-minimum, whose weight is the infimum. Knuth–Bendix completion may fail to terminate, and whether it does can depend on the chosen order $\succ$ of generators. The framework applies to any invertible rearrangement model, including inversions weighted by length and mixtures of inversions and transpositions. The source illustrates it on bacterial genomes.

## Sources

- S. Bhatia, A. Egri-Nagy, S. Serdoz, C. E. Praeger, V. Gebhardt and A. Francis, "A path-deformation framework for determining weighted genome rearrangement distance", arXiv:2008.05560 (2020), Definition 2.1 and Section 5 (Definitions 5.1–5.5, Proposition 5.4, Theorem 5.6, Definition 5.7), <https://doi.org/10.48550/arXiv.2008.05560>.
