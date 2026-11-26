# Finite-path feedback of a relation

In the category of sets and relations with the disjoint union as tensor, let $f : X \sqcup U \to Y \sqcup U$ be a relation. Its [feedback](feedback.md) relates $x \in X$ to $y \in Y$ exactly when either $f$ relates $\mathrm{inl}(x)$ directly to $\mathrm{inl}(y)$, or there are $a, b \in U$ such that $f$ relates $\mathrm{inl}(x)$ to $\mathrm{inr}(a)$, $b$ is reached from $a$ by zero or more hidden steps (each step from $u$ to $u'$ meaning that $f$ relates $\mathrm{inr}(u)$ to $\mathrm{inr}(u')$), and $f$ relates $\mathrm{inr}(b)$ to $\mathrm{inl}(y)$.

In block form, write $A \subseteq X \times Y$, $B \subseteq X \times U$, $D \subseteq U \times U$ and $E \subseteq U \times Y$ for the direct, entry, hidden and exit parts of $f$. Then

$$\operatorname{feedback}(f) = A \cup (B \,;\, D^* \,;\, E),$$

where $;$ is relational composition in forward order and $D^*$ is the reflexive-transitive closure of $D$ (Joyal, Street and Verity, Proposition 6.3).
