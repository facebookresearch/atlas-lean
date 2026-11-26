# Naturality of the trace along an exact pairing

Let $C$ be a symmetric monoidal category with symmetry $\beta$. Let $D$ be a right dual of $U$ through an exact pairing, with coevaluation $\eta_{U,D} : \mathbf{1} \to U \otimes D$ and evaluation $\varepsilon_{U,D} : D \otimes U \to \mathbf{1}$, and write $\operatorname{tr}_D(f) : X \to Y$ for the [trace along this pairing](trace-of-pairing.md) of $f : X \otimes U \to Y \otimes U$. For $f : X \otimes U \to Y \otimes U$, $g : X' \to X$ and $h : Y \to Y'$,

$$\operatorname{tr}_D((h \otimes 1_U) \circ f \circ (g \otimes 1_U)) = h \circ \operatorname{tr}_D(f) \circ g.$$
