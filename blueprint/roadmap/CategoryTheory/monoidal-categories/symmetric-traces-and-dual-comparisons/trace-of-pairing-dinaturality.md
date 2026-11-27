# Dinaturality of the trace along chosen right duals

Let $C$ be a symmetric monoidal category with symmetry $\beta$. Let $U$ and $V$ have chosen right duals $U^\vee$ and $V^\vee$, and write $\operatorname{tr}$ for the [trace along a pairing](trace-of-pairing.md). For $f : X \otimes U \to Y \otimes V$ and $g : V \to U$,

$$\operatorname{tr}_{U^\vee}((1_Y \otimes g) \circ f) = \operatorname{tr}_{V^\vee}(f \circ (1_X \otimes g)).$$

The left side traces out $U$ using its chosen dual, the right side traces out $V$ using its chosen dual. It is the case $k = g^\vee : U^\vee \to V^\vee$ of [sliding](trace-of-pairing-slide.md).
