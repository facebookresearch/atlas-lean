# Whether an inclusion of finitely presented residually finite groups induces an isomorphism of profinite completions is undecidable

No algorithm decides, given finitely presented residually finite groups $P$ and $\Gamma$ and a monomorphism $u : P \hookrightarrow \Gamma$, whether the induced map of profinite completions is an isomorphism, whether it is surjective, or whether the two profinite completions are isomorphic.

For a group $G$ let $\hat{G}$ be its profinite completion; a monomorphism $u : P \to \Gamma$ induces a continuous homomorphism $\hat{u} : \hat{P} \to \hat{\Gamma}$.

**Theorem (Bridson–Wilton).** There are recursive sequences of finite presentations of residually finite groups $P_n = \langle A_n \mid R_n \rangle$ and $\Gamma_n = \langle B_n \mid S_n \rangle$, together with explicit monomorphisms $u_n : P_n \hookrightarrow \Gamma_n$, such that:

1. $\hat{P}_n \cong \hat{\Gamma}_n$ if and only if $\hat{u}_n$ is an isomorphism;
2. $\hat{u}_n$ is an isomorphism if and only if $\hat{u}_n$ is surjective;
3. the set $\{ n \in \mathbb{N} : \hat{P}_n \not\cong \hat{\Gamma}_n \}$ is recursively enumerable but not recursive.

Consequently there is no algorithm that, given a monomorphism $u : P \hookrightarrow \Gamma$ of finitely presented residually finite groups, decides whether $\hat{u}$ is an isomorphism, or whether it is surjective, or whether $\hat{P} \cong \hat{\Gamma}$.

Conventions: the groups $\Gamma_n$ are of the form $H_n \times H_n$ with $H_n$ a residually finite hyperbolic group with a $2$-dimensional classifying space, and $P_n$ is a fiber product. The theorem concerns the profinite completions only; whether the discrete groups $P_n$ and $\Gamma_n$ are themselves isomorphic is a different question, which it does not address.

## Depends on

- [Profinite completion](../profinite-rigidity/profinite-completion.md)
- [Residually finite groups](../../geometric-group-theory/branch-and-thompson-groups/just-infinite-groups/is-residually-finite.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Word-hyperbolic groups](../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Eilenberg–MacLane space](../../../Topology/algebraic-topology/is-eilenberg-maclane-space.md)

## Proof depends on

- [Having a proper finite-index subgroup is undecidable for finitely presented groups](proper-finite-index-subgroup-undecidable.md)

## Expansion

The proof uses a strengthening, proved in the same paper, of the undecidability of profinite triviality: a recursive sequence of aspherical finite combinatorial complexes $K_n$ with $H_1(K_n; \mathbb{Z}) = H_2(K_n; \mathbb{Z}) = 0$ such that the set of $n$ for which $\widehat{\pi_1 K_n}$ is nontrivial is recursively enumerable but not recursive. Wise's residually finite Rips construction applied to $Q_n = \pi_1 K_n$ gives $1 \to N_n \to H_n \to Q_n \to 1$ with $H_n$ residually finite hyperbolic, and the effective 1-2-3 Theorem of Bridson, Howie, Miller and Short produces finite presentations of the fiber products $P_n \subseteq H_n \times H_n$. The induced map of profinite completions is an isomorphism exactly when $\hat{Q}_n$ is trivial. A good expansion links pages for the Rips construction and the effective 1-2-3 Theorem.

## Sources

- Martin R. Bridson and Henry Wilton, *The isomorphism problem for profinite completions of finitely presented, residually finite groups*, Groups Geom. Dyn. 8 (2014), no. 3, 733–745, https://doi.org/10.4171/GGD/245, read in the copy arXiv:1401.2790v1: the statement is Theorem A of its introduction, the strengthened triviality result is Theorem B, and the tools are Theorems 2.1 (Wise) and 2.2 (the effective 1-2-3 Theorem) in Section 2.
