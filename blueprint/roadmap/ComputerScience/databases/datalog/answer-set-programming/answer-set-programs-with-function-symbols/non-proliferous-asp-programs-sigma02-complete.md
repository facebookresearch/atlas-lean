# Deciding whether an answer set program is non-proliferous is Σ⁰₂-complete

Deciding whether a normal program with function symbols has only finitely many finite answer sets is $\Sigma^0_2$-complete, and hardness holds already for frugal programs.

**Theorem.** The set of finite normal programs with function symbols that are *non-proliferous* (have only finitely many finite [answer sets](answer-sets-of-normal-programs.md)) is $\Sigma^0_2$-complete. It remains $\Sigma^0_2$-hard when the input is restricted to frugal programs.

## Depends on

- [Answer sets of normal programs with function symbols](answer-sets-of-normal-programs.md)
- [The arithmetical class $\Sigma_n$](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

None.

## Expansion

*Membership.* Whether a program has at least $n$ finite answer sets is semi-decidable: enumerate finite candidates and check each. With this $\Sigma^0_1$ oracle, a procedure that tries $n = 1, 2, \dots$ and accepts at the first $n$ for which the program has fewer than $n$ finite answer sets semi-decides non-proliferation, so the problem is in $\Sigma^0_2$.

*Hardness.* Universal halting of Turing machines is $\Pi^0_2$-hard; running a machine on all inputs of length at most $n$ shows that "halts on infinitely many inputs" is $\Pi^0_2$-hard, so "halts on only finitely many inputs" is $\Sigma^0_2$-hard. The source writes a program $P_M$ whose answer sets guess a finite binary input word as a chain of terms and encode the computation of $M$ on it; constraints keep only finite words and halting computations. Then $P_M$ has exactly one finite answer set for each input on which $M$ halts and no other answer sets, so $P_M$ is frugal, and it is non-proliferous iff $M$ halts on only finitely many inputs.

## Sources

- Lukas Gerlach, David Carral and Markus Hecher, "Finite Groundings for ASP with Functions: A Journey through Consistency", in *Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence (IJCAI 2024)*, 2024, pp. 3386–3394, <https://doi.org/10.24963/ijcai.2024/375>; read as arXiv:2405.15794v1, <https://arxiv.org/abs/2405.15794v1>: the $\Sigma^0_2$-completeness theorem of Subsection 4.1 with its two lemmas, the remark following them, and the Turing machine simulation in the appendix of that version.
