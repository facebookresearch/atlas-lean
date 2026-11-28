# The sequent calculus LBI

LBI is defined as the bunched sequent calculus for propositional BI: a left and a right introduction rule for every connective except $\bot$, which has only the left rule ($\bot_L$), with antecedents that are bunches, weakening and contraction for the additive combination ";" only, and a cut rule that applies inside any bunch context.

Sequents are $\Gamma \vdash \varphi$ with $\Gamma$ a [bunch](formulas-and-bunches-of-bi.md) and $\varphi$ a BI proposition; $\Gamma(\Delta)$ is a bunch with a distinguished sub-bunch $\Delta$. The rules of LBI are:

Identity, structure and cut:

- (ax) $\varphi \vdash \varphi$;
- ($\equiv$) from $\Gamma \vdash \varphi$ infer $\Delta \vdash \varphi$, where $\Delta \equiv \Gamma$;
- (w) from $\Gamma(\Delta) \vdash \varphi$ infer $\Gamma(\Delta ; \Delta') \vdash \varphi$;
- (c) from $\Gamma(\Delta ; \Delta) \vdash \varphi$ infer $\Gamma(\Delta) \vdash \varphi$;
- (cut) from $\Delta \vdash \varphi$ and $\Gamma(\varphi) \vdash \psi$ infer $\Gamma(\Delta) \vdash \psi$.

Units:

- ($\bot_L$) $\Gamma(\bot) \vdash \varphi$;
- ($\mathrm{I}_L$) from $\Gamma(\emptyset_m) \vdash \varphi$ infer $\Gamma(\mathrm{I}) \vdash \varphi$; ($\mathrm{I}_R$) $\emptyset_m \vdash \mathrm{I}$;
- ($\top_L$) from $\Gamma(\emptyset_a) \vdash \varphi$ infer $\Gamma(\top) \vdash \varphi$; ($\top_R$) $\emptyset_a \vdash \top$.

Multiplicatives:

- ($\ast_L$) from $\Gamma(\varphi , \psi) \vdash \chi$ infer $\Gamma(\varphi \ast \psi) \vdash \chi$; ($\ast_R$) from $\Gamma \vdash \varphi$ and $\Delta \vdash \psi$ infer $\Gamma , \Delta \vdash \varphi \ast \psi$;
- ($\mathrel{-\!\!\ast}_L$) from $\Delta \vdash \varphi$ and $\Gamma(\psi , \Delta') \vdash \chi$ infer $\Gamma(\Delta , \varphi \mathrel{-\!\!\ast} \psi , \Delta') \vdash \chi$; ($\mathrel{-\!\!\ast}_R$) from $\Gamma , \varphi \vdash \psi$ infer $\Gamma \vdash \varphi \mathrel{-\!\!\ast} \psi$.

Additives:

- ($\wedge_L$) from $\Gamma(\varphi ; \psi) \vdash \chi$ infer $\Gamma(\varphi \wedge \psi) \vdash \chi$; ($\wedge_R$) from $\Gamma \vdash \varphi$ and $\Delta \vdash \psi$ infer $\Gamma ; \Delta \vdash \varphi \wedge \psi$;
- ($\to_L$) from $\Delta \vdash \varphi$ and $\Gamma(\psi ; \Delta') \vdash \chi$ infer $\Gamma(\Delta ; \varphi \to \psi ; \Delta') \vdash \chi$; ($\to_R$) from $\Gamma ; \varphi \vdash \psi$ infer $\Gamma \vdash \varphi \to \psi$;
- ($\vee_L$) from $\Gamma(\varphi) \vdash \chi$ and $\Gamma(\psi) \vdash \chi$ infer $\Gamma(\varphi \vee \psi) \vdash \chi$; ($\vee_{R i}$) from $\Gamma \vdash \varphi_i$ infer $\Gamma \vdash \varphi_1 \vee \varphi_2$ ($i = 1, 2$).

A proposition $\varphi$ is a *theorem* of BI if $\emptyset_a \vdash \varphi$ or $\emptyset_m \vdash \varphi$ is provable in LBI; Galmiche, Méry and Pym state, citing Pym, that the theorems are exactly the $\varphi$ with $\emptyset_m \vdash \varphi$ provable.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite outside this folder is needed. The rule ($\vee_L$) is stated here in the corrected form given by Galmiche, Méry and Pym, who note that it was mis-stated in Pym's 2002 monograph; the monograph's errata record the same correction. Galatos, Jipsen, Knudstorp and Ramanayake display the same calculus (their Figure 1) with the rules ($\mathrel{-\!\!\ast}_L$) and ($\to_L$) written without the extra sub-bunch $\Delta'$: the two forms derive the same sequents, since taking $\Delta' = \emptyset_m$ (resp. $\emptyset_a$) and using ($\equiv$) gives theirs, and applying theirs in the context $\Gamma(- , \Delta')$ (resp. $\Gamma(- ; \Delta')$) gives the form here. The relation between LBI and the [natural deduction system NBI](natural-deduction-for-bi.md) is not part of this page.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2, Figure 1 (The LBI Sequent Calculus) with the footnote on the $\vee_L$ rule, Theorem 2.2 and Corollary 2.1.
