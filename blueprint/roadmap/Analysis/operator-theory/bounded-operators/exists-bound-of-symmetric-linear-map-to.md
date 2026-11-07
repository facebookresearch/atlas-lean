# A symmetric linear map from a Banach space to its dual is bounded

Let $E$ be a real
Banach space with dual space $E^*$ of continuous linear functionals, and let $T : E \to E^*$ be
a linear map that is symmetric: $(Tx)(y) = (Ty)(x)$ for all $x, y \in E$. Then $T$ is bounded:
there is a constant $C \ge 0$ such that $\|Tx\| \le C \|x\|$ for all $x \in E$, where $\|Tx\|$
is the operator norm of the functional $Tx$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory of linear operators), `benchmark/level1/ma_proofbench_l1_22.lean` at openbmb/ma-proofbench@31bab4c.
