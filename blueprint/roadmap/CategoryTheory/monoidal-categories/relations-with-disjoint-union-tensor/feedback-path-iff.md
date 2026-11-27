# Terminating paths as entry, hidden steps and exit

In the category of sets and relations with the disjoint union as tensor, let $f : X \sqcup U \to Y \sqcup U$ be a relation, with $U$ the summand fed back. For every $s \in X \sqcup U$ and $y \in Y$, $\mathrm{Path}_f(s, y)$ holds exactly when either $f$ relates $s$ directly to $\mathrm{inl}(y)$, or there are $a, b \in U$ such that $f$ relates $s$ to $\mathrm{inr}(a)$, $b$ is reached from $a$ by zero or more hidden edges ($f$ relating $\mathrm{inr}(u)$ to $\mathrm{inr}(u')$), and $f$ relates $\mathrm{inr}(b)$ to $\mathrm{inl}(y)$.
