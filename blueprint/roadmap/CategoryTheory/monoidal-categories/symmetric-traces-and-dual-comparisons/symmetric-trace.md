# Symmetric traces on a symmetric monoidal category

Let $C$ be a symmetric monoidal category with symmetry $\beta$. A symmetric trace on $C$ assigns to every morphism $f : X \otimes U \to Y \otimes U$ a morphism $\operatorname{Tr}^U(f) : X \to Y$, subject to the following axioms, in which $\alpha$ and $\rho$ are the associator and the right unitor:

- naturality: $\operatorname{Tr}^U((h \otimes 1_U) \circ f \circ (g \otimes 1_U)) = h \circ \operatorname{Tr}^U(f) \circ g$ for $g : X' \to X$ and $h : Y \to Y'$;
- dinaturality: $\operatorname{Tr}^U((1_Y \otimes g) \circ f) = \operatorname{Tr}^V(f \circ (1_X \otimes g))$ for $f : X \otimes U \to Y \otimes V$ and $g : V \to U$;
- vanishing for the unit: $\operatorname{Tr}^{\mathbf{1}}(f) = \rho_Y \circ f \circ \rho_X^{-1}$ for $f : X \otimes \mathbf{1} \to Y \otimes \mathbf{1}$;
- vanishing for tensors: $\operatorname{Tr}^{U \otimes V}(f) = \operatorname{Tr}^U(\operatorname{Tr}^V(\alpha_{Y,U,V}^{-1} \circ f \circ \alpha_{X,U,V}))$ for $f : X \otimes (U \otimes V) \to Y \otimes (U \otimes V)$;
- superposing: $\operatorname{Tr}^U(\alpha_{Z,Y,U}^{-1} \circ (g \otimes f) \circ \alpha_{W,X,U}) = g \otimes \operatorname{Tr}^U(f)$ for $f : X \otimes U \to Y \otimes U$ and $g : W \to Z$;
- yanking: $\operatorname{Tr}^X(\beta_{X,X}) = 1_X$.

## Sources

- A. Joyal, R. Street and D. Verity, Traced monoidal categories, Math. Proc. Cambridge Philos. Soc. 119 (1996), 447–468, specialized to the symmetric case.
