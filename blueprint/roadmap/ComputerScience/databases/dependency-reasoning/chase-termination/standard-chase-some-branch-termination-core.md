# Some-branch termination of the standard chase on all instances is Π⁰₂-complete

Deciding whether, on every instance, some standard chase sequence terminates for a given finite set of tuple-generating dependencies is complete for the class $\Pi^0_2$ of the arithmetical hierarchy, so the problem is undecidable.

**Theorem (Grahne and Onet).** The membership problem for $\mathsf{CT}^{\mathsf{std}}_{\forall\exists}$, that is, given a finite set $\Sigma$ of tuple-generating dependencies, does every instance admit a terminating [standard (restricted) chase sequence](restricted-chase-sequences.md) with $\Sigma$, is $\Pi^0_2$-complete.

In the notation of the page on restricted chase sequences, $\mathsf{CT}^{\mathsf{std}}_{\forall\exists}$ is the class of existentially terminating rule sets. For universal termination the classification is different: all-instances termination of the oblivious and semi-oblivious chase is RE-complete (Gogacz and Marcinkowski), and universal termination of the standard chase on all instances is $\Pi^1_1$-complete (Carral, Gerlach, Larroque and Thomazo). The preprint of the source states the result above as coRE-completeness; the classification is the published one, as recorded in Table 1 and Section 3 of arXiv:2505.16551v1 and in footnote 4 of arXiv:1401.4840v2.

## Depends on

- [Chase variants and their termination classes](chase-variants-and-termination-classes.md)
- [Restricted chase sequences and their termination](restricted-chase-sequences.md)
- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Membership.* Existential termination of a fixed knowledge base is recursively enumerable, by searching for a finite chase sequence; with an oracle for it, enumerating all instances semi-decides the complement of the class, which is therefore in $\Pi^0_2$.

*Hardness.* As for the core chase, the proof translates word rewriting systems into dependencies and words into instances, reducing from uniform termination of word rewriting, which is $\Pi^0_2$-hard; the instance built from a word admits a single restricted chase result encoding all branches of the rewriting computation, and flooding makes every instance terminate when the system is uniformly terminating.

A good expansion links pages for the $\Pi^0_2$-hardness of uniform termination of word rewriting systems and for the recursive enumerability of existential termination of a fixed knowledge base.

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>, cited for the result; the reduction is read in Section 4.2 and the appendix of arXiv:1303.6682v1, <https://arxiv.org/abs/1303.6682v1>, which states the class of the problem incorrectly.
- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; Table 1 ("Restricted", rule set, "Sometimes") and Section 3 ("Related Work") of arXiv:2505.16551v1, the version read, <https://arxiv.org/abs/2505.16551v1>.
- Tomasz Gogacz and Jerzy Marcinkowski, "All-Instances Termination of Chase is Undecidable", in *ICALP 2014, Part II*, Lecture Notes in Computer Science 8573, Springer, 2014, pp. 293–304, <https://doi.org/10.1007/978-3-662-43951-7_25>; footnote 4 of arXiv:1401.4840v2, the version read.
