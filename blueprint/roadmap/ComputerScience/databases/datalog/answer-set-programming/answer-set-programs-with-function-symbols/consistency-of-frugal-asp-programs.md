# Consistency of frugal answer set programs is semi-decidable but undecidable

For normal programs with function symbols that have only finite answer sets, consistency is semi-decidable, and it is already $\Sigma^0_1$-hard for programs that are frugal and have only finitely many answer sets.

**Theorem.**

1. Consistency of frugal programs is in $\Sigma^0_1$: there is a procedure that, given a frugal finite normal program with function symbols, halts exactly when the program has an [answer set](answer-sets-of-normal-programs.md).
2. Consistency is $\Sigma^0_1$-hard already for programs that are both frugal and non-proliferous.

## Depends on

- [Answer sets of normal programs with function symbols](answer-sets-of-normal-programs.md)
- [The arithmetical class $\Sigma_n$](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For item 1, enumerate finite sets of ground atoms and test each for being an answer set; a frugal consistent program has a finite answer set, so the search stops. For item 2, take the Turing machine simulation used for the $\Sigma^0_2$-hardness of non-proliferation but fix the input word by ground facts instead of generating all inputs. The resulting program has a single finite answer set if the machine halts on that input and no answer set otherwise, so it is always frugal and non-proliferous, and its consistency is the halting problem. The difficulty is that even for such programs no bound on the size of the answer set is known in advance.

## Sources

- Lukas Gerlach, David Carral and Markus Hecher, "Finite Groundings for ASP with Functions: A Journey through Consistency", in *Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence (IJCAI 2024)*, 2024, pp. 3386–3394, <https://doi.org/10.24963/ijcai.2024/375>; read as arXiv:2405.15794v1, <https://arxiv.org/abs/2405.15794v1>: the two theorems of Subsection 4.2 ("Consistency becomes (only) Semi-Decidable") of that version.
