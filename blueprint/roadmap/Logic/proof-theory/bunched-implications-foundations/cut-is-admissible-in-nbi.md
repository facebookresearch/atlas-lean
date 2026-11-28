# Cut is admissible in NBI

The cut rule is admissible in the natural deduction system NBI for BI: if $\Gamma(\varphi) \vdash \psi$ and $\Delta \vdash \varphi$ are provable, then so is $\Gamma(\Delta) \vdash \psi$, whether the occurrence of $\varphi$ sits under an additive or a multiplicative combination.

Let $\Gamma(\varphi)$ be a [bunch](formulas-and-bunches-of-bi.md) with a distinguished occurrence of the proposition $\varphi$ as a leaf, $\Delta$ a bunch and $\psi$ a proposition. If $\Gamma(\varphi) \vdash \psi$ and $\Delta \vdash \varphi$ are both provable in [NBI](natural-deduction-for-bi.md), then $\Gamma(\Delta) \vdash \psi$ is provable in NBI, where $\Gamma(\Delta)$ replaces that occurrence of $\varphi$ by $\Delta$:

$$
\frac{\Gamma(\varphi) \vdash \psi \qquad \Delta \vdash \varphi}{\Gamma(\Delta) \vdash \psi}\ (\mathrm{Cut}).
$$

The rule covers both the ";" and the "," cases of bunch construction, because the hole of $\Gamma(-)$ may lie under either combination. In particular, taking $\Gamma(\varphi) = \varphi$, provability between single propositions is transitive: $\chi \vdash \varphi$ and $\varphi \vdash \psi$ give $\chi \vdash \psi$.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [Natural deduction for BI](natural-deduction-for-bi.md)

## Proof depends on

None.

## Expansion

The proof is by induction on the derivation of $\Gamma(\varphi) \vdash \psi$: replace the axiom instance $\varphi \vdash \varphi$ at the distinguished leaf by the derivation of $\Delta \vdash \varphi$, and push the substitution through the other rules. Weakening and contraction on ";" must be handled by substituting into every copy of the affected sub-bunch, and the rule ($\equiv$) by transporting the occurrence along the coherent equivalence. O'Hearn and Pym state the lemma and refer to Pym's sequent presentation and monograph for the connection with cut elimination and normalization, which do not appear here. With the axiom, it makes NBI provability between single propositions a preorder.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2, Lemma 1 and the remark after it.
