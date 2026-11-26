# Verification of a relation between disjoint unions

In the category of sets and relations with the disjoint union as tensor, a relation $f$ acts on assertions by direct image $f[\,\cdot\,]$, and assertions $P_1 \subseteq X$ and $P_2 \subseteq U$ assemble into $P_1 \sqcup P_2 \subseteq X \sqcup U$. Let $F$ be the [powerset verification functor](verification.md), with tensor comparison $\mu$ and its inverse $\delta$. For a relation $f : X \sqcup U \to Y \sqcup V$ and pairs of assertions $P = (P_1, P_2)$ with $P_1 \subseteq X$, $P_2 \subseteq U$ and $R = (R_1, R_2)$ with $R_1 \subseteq Y$, $R_2 \subseteq V$, the comparison-conjugated relation $\delta_{Y,V} \circ F(f) \circ \mu_{X,U}$ relates $P$ to $R$ if and only if

$$f[P_1 \sqcup P_2] \subseteq R_1 \sqcup R_2.$$
