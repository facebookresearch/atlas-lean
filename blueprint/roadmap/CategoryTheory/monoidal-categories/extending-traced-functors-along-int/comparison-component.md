# Comparison components of two functors out of Int

Let $C$ be a symmetric monoidal category with a symmetric trace $T$, let $\mathrm{Int}(T)$ be its [Int construction](../the-int-construction/README.md), whose objects are pairs $X = (X^+, X^-)$ of objects of $C$, and let $J : C \to \mathrm{Int}(T)$, $J(A) = (A, \mathbf{1})$, be the embedding. Let $D$ be a symmetric monoidal category and $K, L : \mathrm{Int}(T) \to D$ braided strong monoidal functors. In $\mathrm{Int}(T)$, $(A, \mathbf{1})$ has the right dual $(\mathbf{1}, A)$ through the [positive pairing](../the-int-construction/positive-pairing.md). Let $i : K \circ J \cong L \circ J$ be a natural isomorphism, with components $i_A : K(A, \mathbf{1}) \to L(A, \mathbf{1})$. For an object $X = (X^+, X^-)$ of $\mathrm{Int}(T)$, the comparison component $c_X : K(X) \to L(X)$ is the composite

$$K(X) \cong K\bigl((X^+, \mathbf{1}) \otimes (\mathbf{1}, X^-)\bigr) \cong K(X^+, \mathbf{1}) \otimes K(\mathbf{1}, X^-) \xrightarrow{i_{X^+} \otimes n_{X^-}} L(X^+, \mathbf{1}) \otimes L(\mathbf{1}, X^-) \cong L\bigl((X^+, \mathbf{1}) \otimes (\mathbf{1}, X^-)\bigr) \cong L(X),$$

built from the decomposition $X \cong (X^+, \mathbf{1}) \otimes (\mathbf{1}, X^-)$, the tensor comparisons of $K$ and $L$, and the [negative comparison](negative-comparison.md) $n_A : K(\mathbf{1}, A) \to L(\mathbf{1}, A)$.
