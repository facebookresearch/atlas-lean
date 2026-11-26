# Trace along a tensor pairing is a repeated trace

Let $C$ be a symmetric monoidal category with symmetry $\beta$. Let $D$ be a right dual of $U$ and $E$ a right dual of $V$ through exact pairings. Then $E \otimes D$ is a right dual of $U \otimes V$, through the tensor pairing: its coevaluation $\mathbf{1} \to U \otimes V \otimes E \otimes D$ nests the coevaluation of $V$ and $E$ inside that of $U$ and $D$, and its evaluation $E \otimes D \otimes U \otimes V \to \mathbf{1}$ first contracts the middle factors $D \otimes U$ and then the remaining $E \otimes V$. For $f : X \otimes (U \otimes V) \to Y \otimes (U \otimes V)$, the [traces along these pairings](trace-of-pairing.md) satisfy

$$\operatorname{tr}_{E \otimes D}(f) = \operatorname{tr}_D\bigl(\operatorname{tr}_E(\alpha_{Y,U,V}^{-1} \circ f \circ \alpha_{X,U,V})\bigr),$$

where $\alpha$ is the associator: after reassociation, $V$ is traced out first, along $E$, and then $U$, along $D$.
