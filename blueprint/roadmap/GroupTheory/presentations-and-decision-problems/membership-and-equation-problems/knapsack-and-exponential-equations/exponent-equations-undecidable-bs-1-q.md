# Systems of exponent equations are undecidable in solvable Baumslag–Solitar groups

For every $q \ge 2$, no algorithm decides whether a system of exponent equations $g_{i1}^{x_{i1}} \cdots g_{id_i}^{x_{id_i}} = h_i$, with exponent variables over $\mathbb{N}$ that may repeat, has a solution in $\mathrm{BS}(1, q)$; knapsack itself is NP-complete there.

Let $\mathrm{BS}(1, q) = \langle a, t \mid t a t^{-1} = a^q \rangle$. A system of exponent equations over a group $G$ is a conjunction

$$
\bigwedge_{i=1}^n g_{i1}^{x_{i1}} g_{i2}^{x_{i2}} \cdots g_{id_i}^{x_{id_i}} = h_i
$$

with $g_{ij}, h_i \in G$ and variables $x_{ij}$ ranging over $\mathbb{N}$, where, unlike in the knapsack problem, a variable may occur several times. $\mathrm{ExpEq}(G)$ asks whether such a system has a solution.

**Theorem.** For every $q \ge 2$, $\mathrm{ExpEq}(\mathrm{BS}(1, q))$ is undecidable (Theorem 5.1 of the source).

The source also proves that the knapsack problem for $\mathrm{BS}(1, q)$ is NP-complete (Theorem 4.1) and that its power word problem is in DLOGTIME-uniform $\mathrm{TC}^0$ (Theorem 3.1, stated for the matrix groups $T(\alpha)$, which include $\mathrm{BS}(1, q)$ as $T(q)$).

## Depends on

- [Knapsack problem for a finitely generated group](knapsack-problem-for-a-group.md)
- [Group](../../../group-basics/group.md)
- [The Baumslag–Solitar group BS(1, n)](../../../profinite-and-topological-groups/subgroup-separability-of-baumslag-solitar-groups/bs1.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

None.

## Expansion

The proof reduces from the existential theory of $(\mathbb{N}, +, (x, y) \mapsto x \cdot 2^y)$, which Büchi and Senger showed undecidable: the proof generalizes to $(x, y) \mapsto x \cdot q^y$, and in $\mathrm{BS}(1, q)$ the atomic formulas become exponent equations: $x + y = z$ as $a^x a^y a^{-z} = 1$, $x < y$ as $\exists z\, a^x a^z a\, a^{-y} = 1$, and $x \cdot q^y = z$ as $t^y a^x t^{-y} a^{-z} = 1$. A good expansion links a page for the Büchi–Senger theorem. Exponent equations govern knapsack for wreath products: knapsack is decidable for $\mathbb{Z} \wr G$ exactly when solvability of systems of exponent equations is decidable for $G$, which the source notes follows from work of Ganardi, König, Lohrey and Zetzsche. Systems of exponent equations are also undecidable for the discrete Heisenberg group (König, Lohrey and Zetzsche).

## Sources

- M. Ganardi, M. Lohrey and G. Zetzsche, "Knapsack and the power word problem in solvable Baumslag–Solitar groups", International Journal of Algebra and Computation 33 (2023), no. 3, 617–639, https://doi.org/10.1142/S0218196723500285; read in arXiv:2002.03837v3, whose numbering is used here (Theorems 3.1, 4.1 and 5.1 and Section 1 of arXiv:2002.03837v3).
