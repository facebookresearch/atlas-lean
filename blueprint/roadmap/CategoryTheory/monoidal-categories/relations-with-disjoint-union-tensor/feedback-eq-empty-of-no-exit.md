# Feedback without any edge into the output is empty

In the category of sets and relations with the disjoint union as tensor, let $f : X \sqcup U \to Y \sqcup U$ be a relation, with $U$ the summand fed back. If for every $s \in X \sqcup U$ and every $y \in Y$ the relation $f$ does not relate $s$ to $\mathrm{inl}(y)$, then the [feedback](feedback.md) of $f$ is empty. The hypothesis covers both the exit block $U \to Y$ and the direct block $X \to Y$: with $U$ empty and one direct edge $x \to y$ there is no edge out of $U$, yet the feedback relates $x$ to $y$.
