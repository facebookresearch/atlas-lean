# Containment of CRPQs under atom-injective semantics is undecidable

Deciding whether one conjunctive regular path query is contained in another when every atom must be matched by a simple path is undecidable, even when the right-hand query uses only finite languages; under standard semantics the problem is EXPSPACE-complete.

**Theorem.** Under atom-injective semantics, the $\mathrm{CRPQ}/\mathrm{CRPQ}$ containment problem and the $\mathrm{CRPQ}/\mathrm{CRPQ}^{\mathrm{fin}}$ containment problem for [conjunctive regular path queries](crpqs-under-injective-semantics.md) are undecidable. That is, no algorithm decides, given CRPQs $Q_1$ and $Q_2$ over the same finite alphabet with free-variable tuples of the same length, their regular expressions written out (with $Q_2$ star-free in the second case), whether $Q_1(G)^{a\text{-}inj} \subseteq Q_2(G)^{a\text{-}inj}$ for every graph database $G$. The proof (Theorem 5.2 of the source) reduces from the Post correspondence problem.

## Depends on

- [Conjunctive regular path queries under injective semantics](crpqs-under-injective-semantics.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces from the Post correspondence problem. From an instance $(u_1, v_1), \dots, (u_\ell, v_\ell)$ it builds Boolean CRPQs $Q_1$ and $Q_2$ of very simple shape, with no infinite language on the right-hand side, such that the instance has a solution if and only if $Q_1 \not\subseteq_{a\text{-}inj} Q_2$. Containment under atom-injective semantics is characterized by atom-injective expansions of $Q_1$: conjunctive queries obtained from an ordinary expansion by identifying pairs of variables that do not lie on a common atom. An intricate encoding makes every counterexample, that is an atom-injective expansion of $Q_1$ admitting no homomorphism from an expansion of $Q_2$ that is injective on each atom, spell out a solution of the instance, with the simple-path requirement doing the work that standard semantics cannot.

The same source shows that under query-injective semantics CRPQ/CRPQ containment is in PSPACE (and PSPACE-complete).

## Sources

- Diego Figueira and Miguel Romero, "Conjunctive Regular Path Queries under Injective Semantics", in *Proceedings of the 42nd ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2023)*, ACM, 2023, pp. 231–240, <https://doi.org/10.1145/3584372.3588664>; read as arXiv:2304.06232v1, <https://arxiv.org/abs/2304.06232v1>: Theorem 5.2 in Section 5 ("Containment for unrestricted CRPQs") with its full proof in the appendix, and Theorem 5.1 (query-injective containment in PSPACE), in the numbering of that version.
