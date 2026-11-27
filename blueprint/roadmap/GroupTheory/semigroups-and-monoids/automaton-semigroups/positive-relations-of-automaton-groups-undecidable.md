# Positive relations of automaton groups are undecidable

No algorithm decides, given an invertible complete automaton, whether some nonempty product of its states, without inverse states, acts as the identity.

Let $\mathcal{T} = (Q, \Sigma, \delta)$ be a G-automaton, that is, a complete and inverse-deterministic [S-automaton](automaton-semigroups.md), generating the automaton group $\mathscr{G}(\mathcal{T})$. The set of *positive relations* of $\mathscr{G}(\mathcal{T})$ with respect to $\mathcal{T}$ is

$$
\mathcal{P}(\mathcal{T}) = \{ \boldsymbol{q} \in Q^+ : \boldsymbol{q} = 1 \text{ in } \mathscr{G}(\mathcal{T}) \},
$$

the set of nonempty state sequences, not containing states of the inverse automaton, that act as the identity.

**Theorem (D'Angeli, Rodaro and Wächter).** It is undecidable, given a G-automaton $\mathcal{T}$, whether $\mathcal{P}(\mathcal{T}) = \varnothing$ (Theorem 3.7 of arXiv:1712.07408v3).

Positive relations depend on the generating automaton, not only on the group. If $\mathcal{P}(\mathcal{T}) = \varnothing$, the semigroup $\mathscr{S}(\mathcal{T})$ is torsion-free. The source also shows that $\mathcal{P}(\mathcal{T})$ is empty exactly when all directed positive orbital graphs centered at non-singular points of $\Sigma^\omega$ are acyclic, so that acyclicity of these orbital graphs is undecidable as well.

## Depends on

- [Automaton semigroups and monoids](automaton-semigroups.md)
- [Group](../../group-basics/group.md)
- [Mealy machine](../../../TheoryOfComputation/regular-languages/automata-and-expressions/sequential-transducers-mealy-and-moore-machines/mealy-machine.md)
- [Automaton group](../../geometric-group-theory/branch-and-thompson-groups/finite-state-automorphisms-of-rooted-trees/automaton-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the Identity Correspondence Problem of Bell and Potapov: given finitely many pairs $(s_i, t_i)$ of elements of the free group on two generators, is there a nonempty sequence of indices with $s_{l_1} \cdots s_{l_k} = t_{l_1} \cdots t_{l_k} = 1$? Using automata of Brunner–Sidki and Šunić–Ventura that realize groups of affine maps given by integer matrices, an instance is turned into a G-automaton whose positive relations correspond to solutions of the instance. A good expansion links the undecidability of the Identity Correspondence Problem, which has no page on main yet.

## Sources

- D. D'Angeli, E. Rodaro and J. P. Wächter, "Automaton semigroups and groups: on the undecidability of problems related to freeness and finiteness", *Israel Journal of Mathematics* 237 (2020), 15–52, doi:10.1007/s11856-020-1972-5; read as arXiv:1712.07408v3, <https://arxiv.org/abs/1712.07408v3>: the definition of $\mathcal{P}(\mathcal{T})$ in Section 3, Theorem 3.7 with its proof, and the abstract, in the numbering of arXiv:1712.07408v3. The erratum included in that version withdraws the freeness results Proposition 3.9, Theorem 3.12 and Corollaries 3.13 and 3.14, not Theorem 3.7.
