# Feedback over the empty hidden set

In the category of sets and relations with the disjoint union as tensor, the tensor unit is the empty set $\varnothing$. For a relation $f : X \sqcup \varnothing \to Y \sqcup \varnothing$, its [feedback](feedback.md) relates $x \in X$ to $y \in Y$ if and only if $f$ relates $\mathrm{inl}(x)$ to $\mathrm{inl}(y)$. Equivalently, $\operatorname{feedback}(f) = \rho_Y \circ f \circ \rho_X^{-1}$, where $\rho_X : X \sqcup \varnothing \to X$ is the right unitor: this is the vanishing axiom for the unit of the [finite-path symmetric trace](symmetric-trace.md).
