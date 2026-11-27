# Sliding a morphism around the trace along exact pairings

Let $C$ be a symmetric monoidal category with symmetry $\beta$. Let $D$ be a right dual of $U$ and $E$ a right dual of $V$ through exact pairings, with coevaluations $\eta$ and evaluations $\varepsilon$, and write $\operatorname{tr}$ for the [trace along a pairing](trace-of-pairing.md). Let $f : X \otimes U \to Y \otimes V$, $g : V \to U$ and $k : D \to E$ satisfy

$$(1_U \otimes k) \circ \eta_{U,D} = (g \otimes 1_E) \circ \eta_{V,E}, \qquad \varepsilon_{V,E} \circ (k \otimes 1_V) = \varepsilon_{U,D} \circ (1_D \otimes g),$$

so that $k$ is dual to $g$. Then $\operatorname{tr}_D((1_Y \otimes g) \circ f) = \operatorname{tr}_E(f \circ (1_X \otimes g))$: the left side traces out $U$ along $D$, the right side traces out $V$ along $E$.
