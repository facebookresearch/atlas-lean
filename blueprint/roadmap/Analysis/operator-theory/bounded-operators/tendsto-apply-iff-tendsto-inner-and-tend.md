# Strong operator convergence characterized by weak operator convergence

Let $H$ be a real
or complex Hilbert space with inner product $\langle \cdot, \cdot \rangle$, let
$(T_n)_{n \in \mathbb{N}}$ be a sequence of bounded linear operators on $H$, let $T$ be a bounded
linear operator on $H$, and write $S^*$ for the adjoint of an operator $S$. Then $T_n \to T$ in
the strong operator topology, that is, $T_n x \to T x$ for every $x \in H$, if and only if both
$T_n \to T$ in the weak operator topology, that is, $\langle y, T_n x \rangle \to
\langle y, T x \rangle$ for all $x, y \in H$, and $T_n^* T_n \to T^* T$ in the weak operator
topology, that is, $\langle y, T_n^* T_n x \rangle \to \langle y, T^* T x \rangle$ for all
$x, y \in H$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General theory of linear operators), `benchmark/level2/ma_proofbench_l2_59.lean` at openbmb/ma-proofbench@31bab4c.
