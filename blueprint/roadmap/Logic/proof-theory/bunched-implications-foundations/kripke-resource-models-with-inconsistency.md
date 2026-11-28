# Kripke resource models with an inconsistent world

A Kripke resource model with an inconsistent world is defined as an elementary resource model of BI whose preordered commutative monoid has a greatest element $\pi$ absorbing every composition; $\pi$ forces every proposition, $\bot$ is forced exactly at $\pi$, and compositions sent to $\pi$ play the part of undefined combinations of resources.

A *Kripke resource monoid* in this sense is a preordered commutative monoid $\mathcal{M} = (M, \bullet, e, \sqsubseteq)$ with $\bullet$ bifunctorial for $\sqsubseteq$ ($m \sqsubseteq n$ and $m' \sqsubseteq n'$ imply $m \bullet m' \sqsubseteq n \bullet n'$) that contains a greatest element $\pi$ ($m \sqsubseteq \pi$ for all $m$) with $\pi \bullet m = \pi$ for all $m \in M$. Here and below, following the source's convention, $m = n$ between worlds means the equivalence $m \sqsubseteq n$ and $n \sqsubseteq m$, so $\pi \bullet m = \pi$ says that $\pi \bullet m$ is equivalent to $\pi$.

A *Kripke resource interpretation* is a map $[\![-]\!] : L \to \wp(M)$ such that for every propositional letter $p$: $m \sqsubseteq n$ and $m \in [\![p]\!]$ imply $n \in [\![p]\!]$ (Kripke monotonicity), and $\pi \in [\![p]\!]$.

A *Kripke resource model* is a triple $\mathcal{K} = (\mathcal{M}, \models, [\![-]\!])$ with $\mathcal{M}$ such a monoid, $[\![-]\!]$ such an interpretation and $\models$ the forcing relation on [BI propositions](formulas-and-bunches-of-bi.md) given by

- $m \models p$ iff $m \in [\![p]\!]$; $m \models \top$ always; $m \models \bot$ iff $m = \pi$ in the sense above, that is, iff $\pi \sqsubseteq m$;
- $m \models \varphi \wedge \psi$ iff $m \models \varphi$ and $m \models \psi$; $m \models \varphi \vee \psi$ iff $m \models \varphi$ or $m \models \psi$;
- $m \models \varphi \to \psi$ iff for all $n$ with $m \sqsubseteq n$, $n \models \varphi$ only if $n \models \psi$;
- $m \models \mathrm{I}$ iff $e \sqsubseteq m$;
- $m \models \varphi \ast \psi$ iff there are $n, n'$ with $n \bullet n' \sqsubseteq m$, $n \models \varphi$ and $n' \models \psi$;
- $m \models \varphi \mathrel{-\!\!\ast} \psi$ iff for all $n$ with $n \models \varphi$, $m \bullet n \models \psi$.

A sequent $\Gamma \vdash \varphi$ is *valid* in this semantics if, in every Kripke resource model, every world forcing $\Phi_\Gamma$ forces $\varphi$.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite is missing. The clauses are those of [elementary Kripke resource models](elementary-kripke-resource-models.md) except for $\bot$; by induction every proposition is forced at every world equivalent to $\pi$ and is upward closed; with literal equality in the clause for $\bot$ this would fail in a preorder having a world $n \ne \pi$ with $\pi \sqsubseteq n$. These models are exactly the basic [Grothendieck resource models](grothendieck-resource-models.md), in which the empty family covers $\pi$ alone. Galmiche, Méry and Pym also give an equivalent formulation with partially defined preordered commutative monoids (PDM models), in which an undefined composition replaces $\pi$, $\bot$ is forced nowhere, and the clauses for $\ast$ and $\mathrel{-\!\!\ast}$ quantify only over defined compositions; separation logic's heap model, in which heaps with overlapping domains have no composition, is the motivating example, as are the [separation algebras](../../../ComputerScience/program-logics-and-verification/separation-logic-metatheory/abstract-separation-logic/separation-algebras.md) of abstract separation logic. The source obtains these models as the instance $R_{\sqsubseteq} xyz \Leftrightarrow x \bullet y \sqsubseteq z$ of its ternary relational semantics.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2.2, Definition 2.8 (the convention that $m = n$ means $m \sqsubseteq n$ and $n \sqsubseteq m$); Section 5.2, Definition 5.5 (KRM with greatest element $\pi$), Definition 5.6 (KRI), Definition 5.7 (Kripke resource model) and Lemma 5.6; Section 5.3, Definition 5.8 (PDM model) and the paragraph before it; Section 5.1, Definition 5.1 (BI frame).
