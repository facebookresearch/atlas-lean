# Soundness and completeness of BI for BI-algebras

BI is sound and complete for BI-algebras: for all BI propositions $\varphi$ and $\psi$, the judgement $\varphi \vdash \psi$ is provable in BI if and only if $[\![\varphi]\!]_A \le [\![\psi]\!]_A$ for every BI-algebra $A$ and every interpretation in $A$.

For all [BI propositions](formulas-and-bunches-of-bi.md) $\varphi, \psi$,

$$
\varphi \vdash \psi \ \text{ is provable in NBI} \iff \varphi \models \psi ,
$$

where provability is in the [natural deduction system NBI](natural-deduction-for-bi.md), with the single proposition $\varphi$ as antecedent bunch, and $\varphi \models \psi$ means $[\![\varphi]\!]_A \le [\![\psi]\!]_A$ for every [BI-algebra](bi-algebras.md) $A$ and every interpretation of the propositional letters in $A$.

In particular a proposition $\psi$ with $\top \vdash \psi$ provable denotes $\top$ in every BI-algebra, and one with $\mathrm{I} \vdash \psi$ provable denotes an element above $\mathrm{I}$ in every BI-algebra.

## Depends on

- [Natural deduction for BI](natural-deduction-for-bi.md)
- [BI-algebras](bi-algebras.md)
- [Cut is admissible in NBI](cut-is-admissible-in-nbi.md)

## Proof depends on

- [Cut is admissible in NBI](cut-is-admissible-in-nbi.md)

## Expansion

Pym, O'Hearn and Yang prove this for a Hilbert-type system HBI whose judgements are $\varphi \vdash \psi$ between single propositions, with the axioms and rules of intuitionistic propositional logic in that form together with associativity, unit and commutativity laws for $\ast$, monotonicity of $\ast$, and the two rules expressing the adjunction between $\ast$ and $\mathrel{-\!\!\ast}$; they state that $\varphi \vdash \psi$ is provable in HBI if and only if it is provable in NBI (their Lemma 1). Soundness is by induction on derivations: each rule is valid because the corresponding Heyting or residuation law holds in every BI-algebra. Completeness is by the Lindenbaum–Tarski construction: the propositions modulo interderivability form a BI-algebra with $[\varphi] \le [\psi]$ if and only if $\varphi \vdash \psi$, $[\varphi] \ast [\psi] = [\varphi \ast \psi]$, $\mathrm{I} = [\mathrm{I}]$ and $[\varphi] \mathrel{-\!\!\ast} [\psi] = [\varphi \mathrel{-\!\!\ast} \psi]$, and the interpretation $p \mapsto [p]$ refutes every unprovable $\varphi \vdash \psi$ (their Lemma 3). That construction needs $\vdash$ to be reflexive and transitive; in NBI transitivity is [cut admissibility](cut-is-admissible-in-nbi.md), which the statement also relies on since $\varphi \vdash \psi$ must be a preorder for $\models$ to match it. Table 2 of the author copy read (dated 29 November 2002) displays no cut or transitivity rule for HBI; the table of the published version was not compared, which is why this page is stated for NBI. The theorem is the BI analogue of soundness and completeness of intuitionistic logic for Heyting algebras, which is not used in the proof. Adding the rule of reductio ad absurdum gives Boolean BI, whose algebraic models are the Boolean BI-algebras; a separate page would state its completeness.

## Sources

- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.1, Table 2 (HBI), Lemma 1 (equivalence of NBI and HBI), Theorem 2 (soundness), Lemma 3 (model existence) and Theorem 4 (completeness).
- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2, Lemma 1 (admissibility of cut).
