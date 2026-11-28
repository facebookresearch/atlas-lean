# Deciding whether an answer set program is frugal is Π¹₁-complete

Deciding whether a normal program with function symbols has only finite answer sets is $\Pi^1_1$-complete, so it is not arithmetical.

**Theorem.** The set of finite normal programs with function symbols all of whose [answer sets](answer-sets-of-normal-programs.md) are finite (*frugal* programs) is $\Pi^1_1$-complete.

## Depends on

- [Answer sets of normal programs with function symbols](answer-sets-of-normal-programs.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Consistency of answer set programs with function symbols is Σ¹₁-complete](asp-consistency-is-sigma11-complete.md)

## Expansion

*Membership.* Modify the machine $\mathcal M_P$ from the consistency proof so that it halts, instead of looping, when it reaches a finite answer set. Then $P$ is frugal iff the modified machine has no run on the empty word that visits its start state infinitely often, a $\Pi^1_1$ property.

*Hardness.* The program $P_{\mathfrak T}$ built from a tiling system in the consistency proof has an infinite answer set (so is not frugal) if $\mathfrak T$ has a recurring solution, and no answer set at all (so is frugal) otherwise. Hence frugality is $\Pi^1_1$-hard.

For frugal programs consistency drops to $\Sigma^0_1$, because an answer set, if one exists, is finite and can be found by enumeration.

A good expansion also links a page for the analytical hierarchy and its class $\Pi^1_1$, which the statement uses.

## Sources

- Lukas Gerlach, David Carral and Markus Hecher, "Finite Groundings for ASP with Functions: A Journey through Consistency", in *Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence (IJCAI 2024)*, 2024, pp. 3386–3394, <https://doi.org/10.24963/ijcai.2024/375>; read as arXiv:2405.15794v1, <https://arxiv.org/abs/2405.15794v1>: Theorem 3 in Section 4.1, with its proof sketch there and in the appendix, in the numbering of that version.
