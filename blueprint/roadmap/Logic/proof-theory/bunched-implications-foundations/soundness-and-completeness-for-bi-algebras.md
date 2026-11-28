# Soundness and completeness of BI for BI-algebras

The sequent calculus LBI is sound and complete for BI-algebras: for all BI propositions $\varphi$ and $\psi$, the sequent $\varphi \vdash \psi$ is provable in LBI if and only if $[\![\varphi]\!]_A \le [\![\psi]\!]_A$ for every BI-algebra $A$ and every interpretation in $A$.

For all [BI propositions](formulas-and-bunches-of-bi.md) $\varphi, \psi$,

$$
\varphi \vdash \psi \ \text{ is provable in LBI} \iff [\![\varphi]\!]_A \le [\![\psi]\!]_A \text{ for every BI-algebra } A \text{ and every interpretation in } A,
$$

where provability is in the [sequent calculus LBI](sequent-calculus-lbi.md), with the single proposition $\varphi$ as antecedent bunch, and the interpretations are those of [BI-algebras](bi-algebras.md), which assign an element to each propositional letter and extend to all propositions connective by connective. More generally, for every bunch $\Gamma$, the sequent $\Gamma \vdash \psi$ is provable in LBI if and only if $[\![\Phi_\Gamma]\!]_A \le [\![\psi]\!]_A$ for every BI-algebra $A$ and every interpretation in $A$, where $\Phi_\Gamma$ is the formula of $\Gamma$.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)
- [BI-algebras](bi-algebras.md)

## Proof depends on

None.

## Expansion

Galatos, Jipsen, Knudstorp and Ramanayake state the single-formula equivalence for the calculus of their Figure 1, which is LBI as on its page (the two presentations of the left rules for the implications derive the same sequents), with all BI-algebras and all homomorphisms from the formula algebra, that is, all interpretations; they derive the bunch form from it by the observation that $\Gamma \vdash \psi$ is provable exactly when $\Phi_\Gamma \vdash \psi$ is, which holds because the left rules for $\wedge$, $\ast$, $\top$ and $\mathrm{I}$ turn $\Gamma \vdash \psi$ into $\Phi_\Gamma \vdash \psi$, while $\Gamma \vdash \Phi_\Gamma$ is derivable by the right rules for the same connectives, so that (cut) turns $\Phi_\Gamma \vdash \psi$ back into $\Gamma \vdash \psi$. Soundness is by induction on derivations, a bunch being read as its formula: each rule is valid because the corresponding Heyting or residuation law holds in every BI-algebra, (cut) because $\le$ is transitive and the operations are monotone, and weakening, contraction and ($\equiv$) because $\wedge$ is a meet with unit $\top$ and $\ast$ is commutative and associative with unit $\mathrm{I}$. Completeness is by the Lindenbaum–Tarski construction: the propositions modulo interderivability in LBI form a BI-algebra with $[\varphi] \le [\psi]$ if and only if $\varphi \vdash \psi$, $[\varphi] \ast [\psi] = [\varphi \ast \psi]$, $\mathrm{I} = [\mathrm{I}]$ and $[\varphi] \mathrel{-\!\!\ast} [\psi] = [\varphi \mathrel{-\!\!\ast} \psi]$, in which the interpretation $p \mapsto [p]$ refutes every unprovable $\varphi \vdash \psi$; provability is a preorder by the axiom and the rule (cut) of LBI, so no cut-elimination result is used. The equivalence is originally due to Pym, O'Hearn and Yang, who prove soundness and completeness (their Theorems 2 and 4) for a Hilbert-type system HBI of judgements between single propositions and relate HBI to the natural deduction system NBI separately (their Lemma 1). The theorem is the BI analogue of soundness and completeness of intuitionistic logic for Heyting algebras, which is not used in the proof. Adding the rule of reductio ad absurdum gives Boolean BI, whose algebraic models are the Boolean BI-algebras; a separate page would state its completeness.

## Sources

- N. Galatos, P. Jipsen, S. B. Knudstorp and R. Ramanayake, "The logic of bunched implications is undecidable", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, Leibniz International Proceedings in Informatics, Schloss Dagstuhl, 2026, article 46, <https://doi.org/10.4230/LIPIcs.LICS.2026.46>: Section 2, Figure 1, Definition 1 and the paragraph after it ($\Gamma \vdash \psi$ provable iff $\Phi_\Gamma \vdash \psi$ is), Definition 2 and the paragraph after Remark 3 (the equivalence for all BI-algebras and all homomorphisms, and its bunch form).
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.1, Table 2 (HBI), Lemma 1 (equivalence of NBI and HBI), Theorem 2 (soundness), Lemma 3 (model existence) and Theorem 4 (completeness).
