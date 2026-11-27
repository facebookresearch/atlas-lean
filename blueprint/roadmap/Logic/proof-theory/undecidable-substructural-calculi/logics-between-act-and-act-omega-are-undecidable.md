# Logics between action logic and infinitary action logic are undecidable

Every set of sequents that contains all theorems of action logic and is contained in infinitary action logic is undecidable. In particular action logic, the inequational theory of residuated Kleene lattices, is undecidable, which answers a question of Kozen.

**Theorem (Kuznetsov).** Let $\mathcal{L}$ be a set of sequents in the language of [action logic](action-logic-and-infinitary-action-logic.md) such that $\mathbf{ACT} \subseteq \mathcal{L} \subseteq \mathbf{ACT}_\omega$. Then membership in $\mathcal{L}$ is undecidable. In particular $\mathbf{ACT}$ itself is undecidable (Corollary 1 of the source).

The source also proves the same for the fragments without $\vee$ and without $\wedge$ (Theorems 6 and 7) and for the extension with the distributive law (Theorem 9); these are separate statements. Without the Kleene star the logic, the multiplicative-additive Lambek calculus, is decidable and PSPACE-complete, and the logic of Kleene algebras (with $\cdot$, $\vee$ and ${}^*$ only) is PSPACE-complete; these boundaries are recalled in the source from other work.

## Depends on

- [Action logic and infinitary action logic](action-logic-and-infinitary-action-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof encodes deterministic Turing machines through the totality property of context-free grammars, following Buszkowski's $\Pi^0_1$-hardness proof for $\mathbf{ACT}_\omega$. For a machine $M$ and input $x$ it builds a sequent $S(M, x)$ such that: if $M$ gets stuck on $x$ in a fixed trivial cycle, $S(M, x)$ is derivable in $\mathbf{ACT}$ (circular behavior has a circular, hence finitary, proof using the fixed-point rule for the star); and if $M$ halts on $x$, $S(M, x)$ is not derivable in $\mathbf{ACT}_\omega$. The set $\mathcal{C}$ of pairs on which the machine trivially cycles and the set $\mathcal{H}$ of pairs on which it halts are recursively inseparable. Any $\mathcal{L}$ between the two logics separates $\{(M, x) : S(M, x) \in \mathcal{L}\}$, which contains $\mathcal{C}$ and is disjoint from $\mathcal{H}$, so it cannot be decidable.

## Sources

- S. Kuznetsov, "Action logic is undecidable", *ACM Transactions on Computational Logic* 22(2):1–26, 2021, doi:10.1145/3445810; read as arXiv:1912.11273v1, <https://arxiv.org/abs/1912.11273v1>: Theorem 2 and Corollary 1 of arXiv:1912.11273v1 and their proof in Section 2.
