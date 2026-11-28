# The first-order theory of free lattices is undecidable

The first-order theory of the class of free lattices, that of the finitely generated free lattices, and the theory of each single free lattice on at least three generators are undecidable, whereas the universal theory of infinite free lattices is decidable.

**Theorem (Nation and Paolini).** In the language $\{\leq\}$:

1. the first-order theory of the class of [free lattices](free-lattices.md) is undecidable;
2. the first-order theory of the class of finitely generated free lattices is undecidable;
3. for every cardinal $\kappa \geq 3$, the first-order theory $\mathrm{Th}(\mathbf{F}_\kappa)$ is undecidable.

The decidability of the universal theory of infinite free lattices is proved in the second paper of the series, J. B. Nation and G. Paolini, "Elementary properties of free lattices II: Decidability of the universal theory", which the source cites in its abstract and Section 1. For $\kappa = 1, 2$ the free lattice is finite (one or four elements), so its theory is decidable; $\mathbf{F}_3$ is the first infinite free lattice. This remark is not in the source; it is in Nation's lecture notes (Chapter 6: $\mathrm{FL}(2)$ has four elements and $\mathrm{FL}(n)$ is infinite for $n \ge 3$).

## Depends on

- [Free lattices](free-lattices.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The ∃∀-theory of finite nice bipartite graphs is hereditarily undecidable](../theories-of-finite-structures/sigma-2-theory-of-restricted-finite-bipartite.md)

## Expansion

The proof reduces from Nies's theorem (1996), as the source recalls, that the $\exists\forall$-theory of finite *nice* bipartite graphs is undecidable (a bipartite graph with parts $A$, $B$ is nice if $|A|, |B| \geq 3$ and every vertex has at least two neighbors and at least one non-neighbor on the other side); equivalently, the $\exists\forall$-theory of finite nice bipartite posets is undecidable. In a free lattice, for a join irreducible element $t$ in canonical form $t = \bigwedge_i \bigvee_j t_{ij}$, the elements in doubly minimal join covers of $t$ are exactly the $t_{ij}$ (Freese, Ježek and Nation), and the relation "$u$ lies in a doubly minimal join cover of $t$" is first-order definable. A first-order formula $\Psi(w)$ then picks out elements $w$ whose set of such $u$ is a nice bipartite poset, every finite nice bipartite poset $Q$ arises in this way at an explicit word $w_Q$ of $\mathbf{F}_\kappa$ for $\kappa \geq |Q|$, and an $\exists\forall$-sentence $\varphi$ about posets translates into a sentence $\varphi_*$ that holds in every free lattice if $\varphi$ holds in all finite nice bipartite posets and fails in $\mathbf{F}_\kappa$ at $w_Q$ if $\varphi$ fails in $Q$. A final step based on Whitman's embedding of $\mathbf{F}_\omega$ into $\mathbf{F}_3$ brings the number of generators down to $3$.

## Sources

- J. B. Nation and G. Paolini, "Elementary properties of free lattices III: Undecidability of the full theory", *Proceedings of the American Mathematical Society* 154(11):4893–4901, 2026, doi:10.1090/proc/17766; read as arXiv:2511.13149v1, <https://arxiv.org/abs/2511.13149v1>: Theorem 1.1 of arXiv:2511.13149v1 and its proof (Fact 2.3 from Nies, Corollary 2.7, Lemmas 3.1–4.4, Theorem 4.5, and Section 5 for $\mathbf{F}_3$).
- J. B. Nation, *Notes on Lattice Theory*, lecture notes, read in the author's open copy at <https://math.hawaii.edu/~jb/math618/LTNotes.pdf>: Chapter 6 (the sizes of $\mathrm{FL}(n)$).
