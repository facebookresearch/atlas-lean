# Hoare triples for morphisms between tensor products

Let $C$ be a monoidal category and $F : C \to \mathbf{MonRel}$ a strong monoidal functor to the [category of preorders and monotone relations](../preorders-and-monotone-relations/README.md), with tensor comparisons $\mu_{X,U} : FX \otimes FU \to F(X \otimes U)$ and their inverses $\delta_{X,U}$; in $\mathbf{MonRel}$, $FX \otimes FU$ is the product preorder $FX \times FU$. A [Hoare triple](triple.md) $\{P\}\, f\, \{Q\}$ for $f : X \to Y$ means that $F(f)$ relates $P$ to $Q$. For $f : X \otimes U \to Y \otimes V$ and pairs of assertions $P \in FX \times FU$ and $Q \in FY \times FV$, the tensor triple $\{P\}\, f\, \{Q\}$ holds exactly when the composite monotone relation

$$\delta_{Y,V} \circ F(f) \circ \mu_{X,U} : FX \times FU \to FY \times FV$$

relates $P$ to $Q$.
