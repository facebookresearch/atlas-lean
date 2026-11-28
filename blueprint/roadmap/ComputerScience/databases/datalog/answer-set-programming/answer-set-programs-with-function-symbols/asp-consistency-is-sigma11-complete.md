# Consistency of answer set programs with function symbols is Σ¹₁-complete

Deciding whether a normal logic program with function symbols has an answer set is complete for the class $\Sigma^1_1$ of the analytical hierarchy.

**Theorem.** The set of finite normal programs with function symbols that have an [answer set](answer-sets-of-normal-programs.md) is $\Sigma^1_1$-complete.

The source recalls that this completeness was proved earlier by Marek, Nerode and Remmel (1994) and by Dantsin, Eiter, Gottlob and Voronkov (2001), and gives a new proof whose hardness part reduces from Finkel's $\Sigma^1_1$-hardness of recurring tilings (2009).

## Depends on

- [Answer sets of normal programs with function symbols](answer-sets-of-normal-programs.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The result goes back to Marek, Nerode and Remmel (Corollary 5.12 there) and appears in the survey of Dantsin, Eiter, Gottlob and Voronkov (Theorem 5.9 there); Gerlach, Carral and Hecher give a new proof by two reductions.

*Membership.* A nondeterministic Turing machine $\mathcal M_P$ builds a candidate answer set by repeatedly choosing a ground rule that the current set of proven atoms violates and adding its head (and recording its negative body). It loops on its start state when the current set is an answer set, and visits the start state once each time the rules that were active at an earlier checkpoint are all satisfied. $P$ is consistent iff some run of $\mathcal M_P$ on the empty word visits the start state infinitely often, a $\Sigma^1_1$ property by Finkel's results on highly undecidable problems for infinite computations.

*Hardness.* A tiling system $\langle T, HI, VI, t_0 \rangle$ (tiles, horizontally and vertically incompatible pairs, a special tile) has a *recurring solution* if some tiling of $\mathbb N \times \mathbb N$ avoids the incompatible pairs and uses $t_0$ infinitely often in the first column; this is $\Sigma^1_1$-hard (Harel; Finkel). The program uses $\mathit{Dom}(c_0)$ and $\mathit{Dom}(s(X)) \leftarrow \mathit{Dom}(X)$ to produce an infinite domain, guesses one tile per grid position with negation, forbids incompatible neighbors by constraints, and forces every position of the first column to lie below an occurrence of $t_0$. The tiling system has a recurring solution iff this program is consistent.

A good expansion links the $\Sigma^1_1$-completeness of recurring solutions of tiling systems (Harel).

## Sources

- Lukas Gerlach, David Carral and Markus Hecher, "Finite Groundings for ASP with Functions: A Journey through Consistency", in *Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence (IJCAI 2024)*, 2024, pp. 3386–3394, <https://doi.org/10.24963/ijcai.2024/375>; read as arXiv:2405.15794v1, <https://arxiv.org/abs/2405.15794v1>: Theorem 1 in Section 3 ("Checking Consistency of ASP Programs"), with Definitions 1–3, Lemmas 1 and 2 and Propositions 1 and 2 of Sections 3.1 and 3.2, in the numbering of that version.
