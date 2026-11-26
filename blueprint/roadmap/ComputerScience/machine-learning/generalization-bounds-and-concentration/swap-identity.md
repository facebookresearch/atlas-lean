# Dataset swap identity

Let $Z$ be a finite set, $n \in \mathbb{N}$, $A$ a map from datasets $S \in Z^n$ to hypotheses, and $\ell(h, z)$ a loss with values in an additive commutative monoid. For every coordinate $i$,

$$\sum_{S \in Z^n} \sum_{z \in Z} \ell\bigl(A(S^{(i \leftarrow z)}), S_i\bigr) = \sum_{S \in Z^n} \sum_{z \in Z} \ell(A(S), z),$$

where $S^{(i \leftarrow z)}$ is $S$ with its $i$-th entry replaced by $z$: the loss of the algorithm trained on the dataset with one entry replaced, evaluated at the replaced entry, sums to the loss of the algorithm trained on the original dataset at a fresh sample. The bijection swaps the fresh sample with the $i$-th entry. This is the swap identity behind uniform-stability generalization bounds.
