# Partial correctness of feedback by a hidden invariant

In the category of sets and relations with the disjoint union as tensor, a relation $f$ acts on assertions by direct image $f[\,\cdot\,]$, and assertions $P_1 \subseteq X$ and $P_2 \subseteq U$ assemble into $P_1 \sqcup P_2 \subseteq X \sqcup U$. For $f : X \sqcup U \to Y \sqcup U$, $P \subseteq X$ and $R \subseteq Y$, the [feedback](../finite-path-feedback-for-disjoint-union-relation/feedback.md) of $f$ maps $P$ into $R$ if and only if some $I \subseteq U$ satisfies

$$f[P \sqcup I] \subseteq R \sqcup I.$$

The invariant $I$ must contain every hidden successor of $P \sqcup I$, and every visible output reached in one step from $P \sqcup I$ must lie in $R$.
