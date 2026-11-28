# Natural deduction for BI

The natural deduction system NBI is defined as the sequent-style system of introduction and elimination rules that derives BI judgements $\Gamma \vdash \varphi$. Paired additive and multiplicative units, conjunctions and implications have rules of the same shape, differing only in combining bunches with ";" or ","; only ";" admits weakening and contraction.

Judgements are $\Gamma \vdash \varphi$ with $\Gamma$ a [bunch](formulas-and-bunches-of-bi.md) and $\varphi$ a BI proposition. *Provability in BI* is derivability by the following rules, where $\Gamma(\Delta)$ is a bunch with a distinguished sub-bunch $\Delta$.

Identity and structure:

- (Axiom) $\varphi \vdash \varphi$;
- ($\equiv$) from $\Gamma \vdash \varphi$ infer $\Delta \vdash \varphi$, where $\Delta \equiv \Gamma$ (coherent equivalence);
- (W) from $\Gamma(\Delta) \vdash \varphi$ infer $\Gamma(\Delta ; \Delta') \vdash \varphi$;
- (C) from $\Gamma(\Delta ; \Delta) \vdash \varphi$ infer $\Gamma(\Delta) \vdash \varphi$.

Multiplicatives:

- ($\mathrm{I}$I) $\emptyset_m \vdash \mathrm{I}$; ($\mathrm{I}$E) from $\Gamma(\emptyset_m) \vdash \chi$ and $\Delta \vdash \mathrm{I}$ infer $\Gamma(\Delta) \vdash \chi$;
- ($\ast$I) from $\Gamma \vdash \varphi$ and $\Delta \vdash \psi$ infer $\Gamma , \Delta \vdash \varphi \ast \psi$; ($\ast$E) from $\Gamma(\varphi , \psi) \vdash \chi$ and $\Delta \vdash \varphi \ast \psi$ infer $\Gamma(\Delta) \vdash \chi$;
- ($\mathrel{-\!\!\ast}$I) from $\Gamma , \varphi \vdash \psi$ infer $\Gamma \vdash \varphi \mathrel{-\!\!\ast} \psi$; ($\mathrel{-\!\!\ast}$E) from $\Gamma \vdash \varphi \mathrel{-\!\!\ast} \psi$ and $\Delta \vdash \varphi$ infer $\Gamma , \Delta \vdash \psi$.

Additives:

- ($\top$I) $\emptyset_a \vdash \top$; ($\top$E) from $\Gamma(\emptyset_a) \vdash \chi$ and $\Delta \vdash \top$ infer $\Gamma(\Delta) \vdash \chi$;
- ($\wedge$I) from $\Gamma \vdash \varphi$ and $\Delta \vdash \psi$ infer $\Gamma ; \Delta \vdash \varphi \wedge \psi$; ($\wedge$E) from $\Gamma(\varphi ; \psi) \vdash \chi$ and $\Delta \vdash \varphi \wedge \psi$ infer $\Gamma(\Delta) \vdash \chi$;
- ($\to$I) from $\Gamma ; \varphi \vdash \psi$ infer $\Gamma \vdash \varphi \to \psi$; ($\to$E) from $\Gamma \vdash \varphi \to \psi$ and $\Delta \vdash \varphi$ infer $\Gamma ; \Delta \vdash \psi$;
- ($\bot$E) from $\Gamma \vdash \bot$ infer $\Gamma \vdash \varphi$;
- ($\vee$I) from $\Gamma \vdash \varphi_i$ infer $\Gamma \vdash \varphi_1 \vee \varphi_2$ ($i = 1, 2$); ($\vee$E) from $\Gamma \vdash \varphi \vee \psi$, $\Delta(\varphi) \vdash \chi$ and $\Delta(\psi) \vdash \chi$ infer $\Delta(\Gamma) \vdash \chi$.

Because ";" admits weakening and contraction, the familiar shared-context forms of ($\wedge$I) and ($\to$E), with both premises over the same $\Gamma$ and conclusion over $\Gamma$, are admissible. There are no weakening or contraction rules for ",".

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite outside this folder is needed. O'Hearn and Pym also state that NBI is strongly normalizing with respect to the evident reductions and commuting conversions (their Proposition 2); cut admissibility has its own page, [cut is admissible in NBI](cut-is-admissible-in-nbi.md), and its sequent-calculus counterpart is [cut elimination for LBI](cut-elimination-for-lbi.md). O'Hearn and Pym also remark that the two implications are not interconvertible: for distinct propositional letters $p, q$, neither $p \mathrel{-\!\!\ast} q \vdash p \to q$ nor $p \to q \vdash p \mathrel{-\!\!\ast} q$ is provable. This is witnessed, through soundness of NBI for bicartesian doubly closed categories, by O'Hearn and Pym's Example 5 ($\mathbf{Set} \times \mathbf{Set}$ with a non-cartesian symmetric monoidal closed structure), where there are no maps in either direction between the two interpreted implications.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2 (the rules, Lemma 1 and Proposition 2) and Section 3 (the non-interconvertibility of the implications and Example 5).
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 2, Table 1 (Natural Deduction System for BI: NBI) and the remarks on weakening and contraction after it.
