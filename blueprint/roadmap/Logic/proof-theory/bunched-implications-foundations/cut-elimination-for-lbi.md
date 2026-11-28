# Cut elimination for LBI

Cut elimination holds for the bunched sequent calculus LBI: every sequent $\Gamma \vdash \varphi$ that is provable in LBI with the cut rule is provable in LBI without it.

Let $\Gamma$ be a [bunch](formulas-and-bunches-of-bi.md) and $\varphi$ a BI proposition. If $\Gamma \vdash \varphi$ is derivable in [LBI](sequent-calculus-lbi.md) using all its rules, including

$$
\frac{\Delta \vdash \psi \qquad \Gamma'(\psi) \vdash \chi}{\Gamma'(\Delta) \vdash \chi}\ (\mathrm{cut}),
$$

then $\Gamma \vdash \varphi$ has a derivation in LBI with no instance of (cut). The cut formula $\psi$ may occur anywhere in the bunch $\Gamma'(\psi)$, inside either kind of combination, and the structural rules (w), (c) and ($\equiv$) remain available in the cut-free derivation. No bound on the size of the cut-free derivation is part of the statement.

## Depends on

- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

The proof is a Gentzen-style argument, by induction on the cut formula and on the heights of the premises, permuting cuts upwards; for LBI it must handle a cut formula inside an arbitrary bunch context and the interaction of contraction on ";" with the cut, and it is given in Pym's monograph, which Galmiche, Méry and Pym cite for this theorem. Sources that use this result to prove unprovability, such as the [incompleteness of the elementary resource semantics with $\bot$](elementary-resource-semantics-is-incomplete-with-bottom.md), rely on the subformula property of cut-free derivations, which follows because every rule other than (cut) has premises built from subformulas of its conclusion. The analogous admissibility of cut for [natural deduction NBI](natural-deduction-for-bi.md) is O'Hearn and Pym's Lemma 1.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Theorem 2.1 (Cut-elimination) and Figure 1.
- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2, Lemma 1 and the paragraph after it, which points to the sequent presentation and its cut elimination.
