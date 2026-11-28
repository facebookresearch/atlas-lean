# Elementary Kripke resource models

An elementary Kripke resource model of BI is defined as a preordered commutative monoid of worlds, or resources, with a monotone interpretation of the propositional letters; additives are forced as in Kripke's semantics of intuitionistic logic, multiplicatives by splitting a world as in Urquhart's semantics, and $\bot$ is forced nowhere.

A *Kripke resource monoid* (KRM) is a structure $\mathcal{M} = (M, \bullet, e, \sqsubseteq)$ in which $(M, \bullet, e)$ is a commutative monoid and $\sqsubseteq$ is a preorder on $M$ such that $\bullet$ is *bifunctorial* (order-preserving): $m \sqsubseteq n$ and $m' \sqsubseteq n'$ imply $m \bullet m' \sqsubseteq n \bullet n'$. The aggregation condition, $m \sqsubseteq m \bullet n$ and $n \sqsubseteq m \bullet n$ for all $m, n$, is not imposed, and $e$ need not be a least or greatest element.

An *elementary Kripke resource interpretation* is a map $[\![-]\!] : L \to \wp(M)$ on propositional letters such that, for all $m, n \in M$ with $m \sqsubseteq n$, $m \in [\![p]\!]$ entails $n \in [\![p]\!]$ (condition (K)). An *elementary Kripke resource model* is a triple $\mathcal{K} = (\mathcal{M}, \models, [\![-]\!])$ with $\mathcal{M}$ a KRM, $[\![-]\!]$ such an interpretation, and $\models \subseteq M \times \mathcal{P}(L)$ the forcing relation on [BI propositions](formulas-and-bunches-of-bi.md) defined by

- $m \models p$ iff $m \in [\![p]\!]$;
- $m \models \top$ always; $m \models \bot$ never;
- $m \models \varphi \wedge \psi$ iff $m \models \varphi$ and $m \models \psi$; $m \models \varphi \vee \psi$ iff $m \models \varphi$ or $m \models \psi$;
- $m \models \varphi \to \psi$ iff for all $n \in M$ with $m \sqsubseteq n$, $n \models \varphi$ only if $n \models \psi$;
- $m \models \mathrm{I}$ iff $e \sqsubseteq m$;
- $m \models \varphi \ast \psi$ iff there are $n, n' \in M$ with $n \bullet n' \sqsubseteq m$, $n \models \varphi$ and $n' \models \psi$;
- $m \models \varphi \mathrel{-\!\!\ast} \psi$ iff for all $n \in M$ with $n \models \varphi$, $m \bullet n \models \psi$.

A sequent $\Gamma \vdash \varphi$ is *valid in* $\mathcal{K}$, written $\Gamma \models_{\mathcal{K}} \varphi$, if for every world $m$, $m \models \Phi_\Gamma$ only if $m \models \varphi$, where $\Phi_\Gamma$ is the formula of the bunch $\Gamma$; it is *valid*, $\Gamma \models \varphi$, if it is valid in every elementary Kripke resource model.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite is missing. By induction on propositions, condition (K) extends from letters to all propositions: $m \sqsubseteq n$ and $m \models \varphi$ imply $n \models \varphi$. Pym, O'Hearn and Yang give the same semantics with the order reversed (Kripke monotonicity downwards, $m \models \mathrm{I}$ iff $m \sqsubseteq e$, and $m \sqsubseteq n \circ n'$ in the clause for $\ast$); replacing $\sqsubseteq$ by its converse maps one class of models onto the other and preserves validity. O'Hearn and Pym's original clauses (1999, Section 5) use a partially ordered commutative monoid with the same downward convention. With the discrete order the multiplicative clauses are Urquhart's semantics of multiplicative intuitionistic linear logic. The semantics is [sound](soundness-of-elementary-resource-semantics.md) for LBI and [complete without $\bot$](completeness-of-elementary-resource-semantics-without-bottom.md); the failure with $\bot$ is [incompleteness with $\bot$](elementary-resource-semantics-is-incomplete-with-bottom.md).

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2.1, Definition 2.3 (KRM), Definition 2.4 (EKRI), Definition 2.5 (EKRM) and the definition of validity after it.
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Sections 3.2 and 3.4 (the downward convention).
- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 5 (Kripke resource semantics).
