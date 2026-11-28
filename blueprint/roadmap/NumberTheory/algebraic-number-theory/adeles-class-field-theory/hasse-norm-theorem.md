# Hasse norm theorem for cyclic extensions

Let $L/K$ be a cyclic extension of number fields and let $a \in K^\times$. For each place $v$ of $K$
choose a place $w$ of $L$ above $v$. Then $a$ is a norm from $L_w^\times$ to $K_v^\times$ for all but
finitely many $v$; and if $a$ is a norm from $L_w^\times$ for every place $v$ of $K$, then
$a = N_{L/K}(b)$ for some $b \in L^\times$.

Because $L/K$ is Galois, whether $a$ is a local norm at $v$ does not depend on the choice of $w$
above $v$. The cyclic hypothesis cannot be dropped: Milne's Remark VIII.3.2 recalls that $5^2$ is a
local norm everywhere from $\mathbb{Q}(\sqrt{13}, \sqrt{17})$ but not a global norm.

Milne's proof: for a cyclic extension the [Tate cohomology group](cohomology-of-idele-classes/cyclic-extension-tate-cohomology.md)
$\hat H^{-1}(G, C_L)$ of the idèle class group vanishes, so the long exact cohomology sequence of
$1 \to L^\times \to \mathbb{I}_L \to C_L \to 1$ shows that
$\hat H^0(G, L^\times) \to \hat H^0(G, \mathbb{I}_L)$ is injective. This map is
$K^\times / N_{L/K}(L^\times) \to \bigoplus_v K_v^\times / N_{L_w/K_v}(L_w^\times)$, by the
[cohomology of the idèle group](cohomology-of-idele-classes/cohomology-of-the-idele-group.md) (Milne,
Proposition VII.2.5).

## Proof depends on

- [Tate cohomology of the idèle class group of a cyclic extension](cohomology-of-idele-classes/cyclic-extension-tate-cohomology.md), for $\hat H^{-1}(G, C_L) = 0$
- [Cohomology of the idèle group of a Galois extension](cohomology-of-idele-classes/cohomology-of-the-idele-group.md), for $\hat H^0(G, \mathbb{I}_L) \cong \bigoplus_v K_v^\times / N_{L_w/K_v}(L_w^\times)$

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VIII.3.1 (Hasse norm theorem) with its
  proof, and Remark VIII.3.2.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.mem_range_norm_iff_forall_local`, and its
  quadratic case as `GroundTheory.Global.mem_range_norm_iff_forall_local_of_finrank_eq_two`.
