# Partial correctness of feedback by a hidden invariant

In the category of sets and relations with the disjoint union as tensor, a relation $f$ acts on assertions by direct image $f[\,\cdot\,]$, and assertions $P_1 \subseteq X$ and $P_2 \subseteq U$ assemble into $P_1 \sqcup P_2 \subseteq X \sqcup U$. For $f : X \sqcup U \to Y \sqcup U$, $P \subseteq X$ and $R \subseteq Y$, the [feedback](../relations-with-disjoint-union-tensor/feedback.md) of $f$ maps $P$ into $R$ if and only if some $I \subseteq U$ satisfies

$$f[P \sqcup I] \subseteq R \sqcup I.$$

The invariant $I$ must contain every hidden successor of $P \sqcup I$, and every visible output reached in one step from $P \sqcup I$ must lie in $R$.

Equivalently, the [powerset verification functor](verification.md) $F$ preserves the traces: it sends the [finite-path trace](../relations-with-disjoint-union-tensor/symmetric-trace.md) on relations to the [existential trace](../preorders-and-monotone-relations/symmetric-trace.md) on monotone relations, $F(\operatorname{feedback}(f)) = \operatorname{Tr}^{FU}(\delta_{Y,U} \circ F(f) \circ \mu_{X,U})$ for every $f$. At a pair $(P, R)$ the left side holds exactly when $\operatorname{feedback}(f)[P] \subseteq R$, and the right side exactly when some $I \subseteq U$ has $f[P \sqcup I] \subseteq R \sqcup I$, by the [comparison relation](comparison-rel.md).
