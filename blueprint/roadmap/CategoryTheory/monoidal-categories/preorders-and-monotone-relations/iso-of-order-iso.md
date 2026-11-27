# Order isomorphisms as isomorphisms of monotone relations

In the category of preorders and monotone relations, a morphism $X \to Y$ is a relation $R \subseteq X \times Y$ that is closed downward in $X$ and upward in $Y$, and the [graph](graph.md) of a monotone map $f$ is the upward-closed relation $\{(x, y) : f(x) \le y\}$, not the equality graph (even the identity on $0 < 1$ relates $0$ to $1$). An order isomorphism $e : X \cong Y$ induces an isomorphism $X \cong Y$ whose forward relation is $\{(x, y) : e(x) \le y\}$ and whose inverse is $\{(y, x) : e^{-1}(y) \le x\}$.
