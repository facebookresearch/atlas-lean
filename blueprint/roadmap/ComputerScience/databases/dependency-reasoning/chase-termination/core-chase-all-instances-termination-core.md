# All-instances termination of the core chase is Π⁰₂-complete

Deciding whether the core chase terminates on every instance for a given finite set of tuple-generating dependencies is complete for the class $\Pi^0_2$ of the arithmetical hierarchy, so the problem is undecidable.

**Theorem (Grahne and Onet).** The membership problem for $\mathsf{CT}^{\mathsf{core}}_{\forall\forall}$, that is, given a finite set $\Sigma$ of tuple-generating dependencies, does the [core chase](chase-variants-and-termination-classes.md) with $\Sigma$ terminate on every instance, is $\Pi^0_2$-complete.

The dependencies are part of the input; constants may occur in them. For a fixed instance $I$, termination of the core chase on $I$ is RE-complete (Deutsch, Nash and Remmel). Since all core chase sequences of an instance are finite or all are infinite, the classes $\mathsf{CT}^{\mathsf{core}}_{\forall\forall}$ and $\mathsf{CT}^{\mathsf{core}}_{\forall\exists}$ coincide. The preprint of the source states the result as coRE-completeness; the classification above is the published one, as recorded by Carral, Gerlach, Larroque and Thomazo (Table 1 and Section 3 of arXiv:2505.16551v1), and Gogacz and Marcinkowski point out the same correction for the standard chase (footnote 4 of arXiv:1401.4840v2).

## Depends on

- [Chase variants and their termination classes](chase-variants-and-termination-classes.md)
- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Membership.* A set $\Sigma$ is outside $\mathsf{CT}^{\mathsf{core}}_{\forall\forall}$ exactly when the core chase does not terminate on some instance. Termination on a fixed instance is recursively enumerable, so with an oracle for it one can semi-decide the complement by enumerating all instances; hence the class is in $\Pi^0_2$.

*Hardness.* The reduction is from uniform termination of word rewriting systems (does the system terminate on every input word), which is $\Pi^0_2$-hard. A word rewriting system $R$ is translated into dependencies $\Sigma_R$ and each word $w$ into an instance $D_w$ such that $R$ terminates on $w$ exactly when the chase terminates on $D_w$; a flooding construction makes the chase with $\Sigma_R$ terminate on every instance when $R$ is uniformly terminating, and the same reduction serves the core chase and the standard chase.

A good expansion links pages for the $\Pi^0_2$-hardness of uniform termination of word rewriting systems and for the recursive enumerability of core chase termination on a fixed instance.

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>, cited for the result; the reduction is read in Section 4.2 and the appendix of arXiv:1303.6682v1, <https://arxiv.org/abs/1303.6682v1>, which states the class of the problem incorrectly.
- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; Table 1 ("Core", rule set) and Section 3 ("Related Work"), which give the $\Pi^0_2$ upper bound and the hardness by Grahne and Onet's reduction, of arXiv:2505.16551v1, the version read, <https://arxiv.org/abs/2505.16551v1>.
- Tomasz Gogacz and Jerzy Marcinkowski, "All-Instances Termination of Chase is Undecidable", in *ICALP 2014, Part II*, Lecture Notes in Computer Science 8573, Springer, 2014, pp. 293–304, <https://doi.org/10.1007/978-3-662-43951-7_25>; footnote 4 of arXiv:1401.4840v2, the version read.
