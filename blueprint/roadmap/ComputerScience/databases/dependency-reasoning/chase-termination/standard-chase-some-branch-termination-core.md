# Some-branch termination of the standard chase on all instances is coRE-complete

Deciding whether, on every instance, some standard chase sequence terminates for a given finite set of tuple-generating dependencies is coRE-complete.

**Theorem (Grahne and Onet).** The membership problem for $\mathsf{CT}^{\mathsf{std}}_{\forall\exists}$, that is, given a finite set $\Sigma$ of tuple-generating dependencies, does every instance admit a terminating standard chase sequence with $\Sigma$, is coRE-complete.

The reduction behind this theorem does not apply to $\mathsf{CT}^{\mathsf{std}}_{\forall\forall}$, $\mathsf{CT}^{\mathsf{sobl}}_{\forall\forall}$ or $\mathsf{CT}^{\mathsf{obl}}_{\forall\forall}$. For those classes the authors obtain coRE-completeness only when $\Sigma$ may also contain a denial constraint $\alpha \to \bot$ (their Theorem 8), and they leave open whether the denial constraint can be dropped.

## Depends on

- [Chase variants and their termination classes](chase-variants-and-termination-classes.md)
- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

As for the core chase, the proof translates word rewriting systems into tgds and words into instances, reducing from uniform termination of word rewriting, which is coRE-complete (Huet and Lankford) and has no page here.

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>; Theorem 7 (main statement) and Theorem 8 (denial constraints) in Section 4.2 of arXiv:1303.6682v1 (the copy read), <https://arxiv.org/abs/1303.6682v1>.
