# Lifting resolution depth to semantic cutting planes depth

Composing a CNF formula with the 4-bit XOR gadget turns resolution depth into semantic cutting planes depth up to a factor $2$; consequently Tseitin formulas on expanders require linear depth in semantic cutting planes.

A **semantic cutting planes** refutation of an $n$-variate unsatisfiable CNF $F$, in top-down form, is a DAG of fan-out at most $2$ whose nodes carry halfspaces $H_v \subseteq \mathbb{R}^n$: the unique source carries $\mathbb{R}^n$; for an internal node $u$ with children $v, w$, $H_u \cap \{0,1\}^n \subseteq H_v \cup H_w$; and each sink $u$ is labelled by a clause $C \in F$ with $H_u \cap \{0,1\}^n \subseteq C^{-1}(0)$. For a CNF $F$ on $z_1, \dots, z_n$, $F \circ \mathrm{XOR}_4^n$ substitutes $z_i := x_{i,1} \oplus x_{i,2} \oplus x_{i,3} \oplus x_{i,4}$ and expands into CNF.

**Theorem.** For every unsatisfiable CNF formula $F$,

$$
\mathrm{depth}_{\mathrm{sCP}}(F \circ \mathrm{XOR}_4^n) \ge \tfrac{1}{2}\, \mathrm{depth}_{\mathrm{Res}}(F).
$$

**Unlifted version.** If $F$ is a system of $\mathbb{F}_2$-linear equations whose constraint-variable graph is an $(r, s+3)$-boundary expander, then $\mathrm{depth}_{\mathrm{sCP}}(F) \ge rs/2$. In particular, for all sufficiently large $n$ there are a graph $G$ on $n$ vertices and a labelling $\ell$ such that the Tseitin formula of $(G, \ell)$ requires depth $\Omega(n)$ in semantic cutting planes, and random $k$-XOR and $k$-CNF formulas with $k \ge 6$ and $O(n)$ constraints require depth $\Omega(n)$ with high probability.

## Expansion

Resolution depth equals the number of rounds a Prover needs to falsify an axiom in the Prover-Adversary game. Walk down a semantic CP refutation of $F \circ \mathrm{XOR}_4^n$ keeping a partial restriction $\rho$ that is block-closed, keeps the current halfspace good (containing the all-$\frac{1}{2}$ point after restriction) and is consistent with an optimal Adversary. A covering lemma shows that one child halfspace stays good after fixing at most two more coordinates; the touched blocks are then fixed to values chosen by the Adversary using a lemma that good halfspaces can be restricted to satisfy any parity on a block of at least two free variables. Each step fixes at most two blocks, so a leaf cannot be reached before $\mathrm{depth}_{\mathrm{Res}}(F)/2$ steps. The unlifted version replaces block-closedness by preservation of boundary expansion.

## Depends on

None.

## Proof depends on

None.

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019 (arXiv version read: Section 5.1, the depth-lifting theorem and the Prover-Adversary characterization of resolution depth; Section 5.2, the boundary-expander theorem; Section 5.4, the Tseitin and random formula applications).
