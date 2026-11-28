# Modal logics of RCC8 relations over full region structures are Π¹₁-hard

For full concrete region structures of regular closed or convex regions, the modal logic of the RCC8 relations is $\Pi^1_1$-hard and hence not recursively enumerable, so it has no recursive axiomatization.

**Theorem (Lutz and Wolter).** The [modal logics of topological relations](modal-logics-of-topological-relations.md) $L_{\mathrm{RCC8}}(\mathcal{TOP})$ and $L_{\mathrm{RCC8}}(\mathbb{R}^n, U_n)$ with $U_n \in \{\mathbb{R}^n_{\mathrm{reg}}, \mathbb{R}^n_{\mathrm{conv}}\}$ and $n \geq 1$ are $\Pi^1_1$-hard: every $\Pi^1_1$ set many-one reduces to each of them. In particular none of them is recursively enumerable.

By contrast, the logics of substructures of these concrete region structures are recursively enumerable (for $\mathbb{R}^n_{\mathrm{reg}}$ and $\mathbb{R}^n_{\mathrm{rect}}$; open for $\mathbb{R}^n_{\mathrm{conv}}$), so restricting to substructures lowers the complexity from $\Pi^1_1$-hard to r.e., although these logics stay undecidable.

## Depends on

- [Modal logics of topological relations](modal-logics-of-topological-relations.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Modal logics of RCC8 relations over Euclidean regions are undecidable](modal-logics-of-rcc8-relations-are-undecidable.md)

## Expansion

The undecidability reduction is extended to the recurrent domino problem, in which a distinguished tile $t_0$ must occur infinitely often in the first column; Harel showed this variant $\Sigma^1_1$-hard. An extra conjunct forces an infinite sequence of regions $r_1, r_2, \dots$ with $r_i \mathrel{\mathrm{ntpp}} r_{i+1}$, all on the wall and carrying $t_0$; for the full structures listed, a model of the extended formula exists whenever the recurrent domino system has a solution. Satisfiability is thus $\Sigma^1_1$-hard and validity $\Pi^1_1$-hard.

## Sources

- C. Lutz and F. Wolter, "Modal logics of topological relations", *Logical Methods in Computer Science* 2(2), Paper 5, 2006, doi:10.2168/LMCS-2(2:5)2006; read as arXiv:cs/0605064v2, <https://arxiv.org/abs/cs/0605064v2>: Theorem 15 in Section 6 of arXiv:cs/0605064v2 and its proof, with Theorems 13 and 14 (recursive enumerability) of the same section.
