# The multiplier ring of an ideal coprime to the conductor

Let $K$ be a number field with
ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`), let $O$ be an order in $K$
(`NumberField.IsOrder`), and let
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$ be its conductor, the
conductor ideal (`Subalgebra.conductorIdeal`) of $O$ viewed as a subring of $\mathcal{O}_K$. Let
$\mathfrak{b}$ be a nonzero ideal of $O$ with $\mathfrak{b} + \mathfrak{c} = O$, where
$\mathfrak{c} \subseteq O$ is viewed as an ideal of $O$ (its preimage under
$O \hookrightarrow \mathcal{O}_K$). Then

$$\{x \in K : x\mathfrak{b} \subseteq \mathfrak{b}\} = O.$$

This is K. Conrad, *The conductor ideal of an order*, Theorem 3.1 (p. 5), with the conductor of
Definition 1.1 (p. 1).
