# Unfolding a terminating execution

In the category of sets and relations with the disjoint union as tensor, let $f : X \sqcup U \to Y \sqcup U$ be a relation. For $s \in X \sqcup U$ and $y \in Y$, there is a [terminating execution](feedback-path.md) from $s$ to $y$ if and only if either $f$ relates $s$ to $\mathrm{inl}(y)$, or $f$ relates $s$ to $\mathrm{inr}(a)$ for some $a \in U$ and there is a terminating execution from $\mathrm{inr}(a)$ to $y$. After one hidden step the remainder is again a terminating execution, not necessarily an immediate exit.
