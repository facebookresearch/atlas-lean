# All-instances termination of the core chase is coRE-complete

Deciding whether the core chase terminates on every instance for a given finite set of tuple-generating dependencies is coRE-complete, so the problem is undecidable but its complement is recursively enumerable.

**Theorem (Grahne and Onet).** The membership problem for $\mathsf{CT}^{\mathsf{core}}_{\forall\forall}$, that is, given a finite set $\Sigma$ of tuple-generating dependencies, does the core chase with $\Sigma$ terminate on every instance, is coRE-complete.

The dependencies are part of the input; constants may occur in them. The same reduction shows that, for a fixed instance $I$, membership in $\mathsf{CT}^{\mathsf{core}}_{I,\forall}$ (termination of the core chase on $I$) is RE-complete, as the authors note in agreement with Deutsch, Nash and Remmel.

## Depends on

- [Chase variants and their termination classes](chase-variants-and-termination-classes.md)
- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

The reduction is from uniform termination of word rewriting systems (does the system terminate on every input word), which is coRE-complete by Huet and Lankford. A word rewriting system is translated into tgds and each word into an instance so that the system terminates on the word if and only if the core chase terminates on the instance, and the full proof (in the appendix) relates uniform termination of the system to termination of the core chase on all instances. Uniform termination of word rewriting has no page here.

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>; Theorem 6 (main statement), the corollary after it, and the discussion opening Section 4.2 of arXiv:1303.6682v1 (the copy read), <https://arxiv.org/abs/1303.6682v1>.
