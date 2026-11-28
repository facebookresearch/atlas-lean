# Grothendieck resource models

A Grothendieck resource model of BI is defined as a preordered commutative monoid of worlds with a Grothendieck topology that respects the monoid operation; disjunction, the unit $\mathrm{I}$ and $\ast$ are forced locally on covers, and $\bot$ is forced at a world exactly when the empty family covers it.

A *Grothendieck topological monoid* (GTM) is a quintuple $\mathcal{M} = (M, \bullet, e, \sqsubseteq, J)$ in which $(M, \bullet, e, \sqsubseteq)$ is a preordered commutative monoid with $\bullet$ bifunctorial for $\sqsubseteq$ ($m \sqsubseteq n$ and $m' \sqsubseteq n'$ imply $m \bullet m' \sqsubseteq n \bullet n'$), and $J : M \to \wp(\wp(M))$ satisfies, for all $m, n \in M$:

- (Sieve) if $S \in J(m)$ and $n \in S$ then $m \sqsubseteq n$;
- (Maximality) if $m = n$, meaning $m \sqsubseteq n$ and $n \sqsubseteq m$, then $\{n\} \in J(m)$;
- (Stability) if $m \sqsubseteq n$ and $S \in J(m)$, there is $T \in J(n)$ such that for every $t \in T$ there is $s \in S$ with $s \sqsubseteq t$;
- (Transitivity) if $S \in J(m)$ and $S_n \in J(n)$ for each $n \in S$, then $\bigcup_{n \in S} S_n \in J(m)$;
- (Continuity) if $S \in J(m)$ then $\{ k \bullet n \mid k \in S \} \in J(m \bullet n)$.

A *Grothendieck topological interpretation* is a map $[\![-]\!] : L \to \wp(M)$ such that, for every letter $p$: (K) $m \sqsubseteq n$ and $m \in [\![p]\!]$ imply $n \in [\![p]\!]$; (Sh) if $S \in J(m)$ and $n \in [\![p]\!]$ for all $n \in S$, then $m \in [\![p]\!]$. A *Grothendieck resource model* (GRM) is a triple $\mathcal{G} = (\mathcal{M}, \models, [\![-]\!])$ with $\mathcal{M}$ a GTM, $[\![-]\!]$ such an interpretation and $\models$ the forcing relation on [BI propositions](formulas-and-bunches-of-bi.md) given by

- $m \models p$ iff $m \in [\![p]\!]$; $m \models \top$ always; $m \models \bot$ iff $\emptyset \in J(m)$;
- $m \models \varphi \wedge \psi$ iff $m \models \varphi$ and $m \models \psi$;
- $m \models \varphi \vee \psi$ iff there is $S \in J(m)$ such that every $m' \in S$ satisfies $m' \models \varphi$ or $m' \models \psi$;
- $m \models \varphi \to \psi$ iff for all $n$ with $m \sqsubseteq n$, $n \models \varphi$ only if $n \models \psi$;
- $m \models \mathrm{I}$ iff there is $S \in J(m)$ with $e \sqsubseteq m'$ for all $m' \in S$;
- $m \models \varphi \ast \psi$ iff there is $S \in J(m)$ such that for every $m' \in S$ there are $n, n'$ with $n \bullet n' \sqsubseteq m'$, $n \models \varphi$ and $n' \models \psi$;
- $m \models \varphi \mathrel{-\!\!\ast} \psi$ iff for all $n$ with $n \models \varphi$, $m \bullet n \models \psi$.

A sequent $\Gamma \vdash \varphi$ is *valid in* $\mathcal{G}$ if every world forcing $\Phi_\Gamma$ forces $\varphi$, and *valid*, $\Gamma \models \varphi$, if it is valid in every GRM.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite is missing. Conditions (K) and (Sh) extend from letters to all propositions, which makes the forcing relation well defined as a sheaf semantics (Pym, O'Hearn and Yang, Lemmas 16 and 17). A world covered by the empty family forces every proposition, since (Sh) holds vacuously. Galmiche, Méry and Pym call a GRM *basic* when $M$ has a greatest element $\pi$ with $\pi \bullet m = \pi$ for all $m$, and $S \in J(m)$ holds exactly when either $S \ne \emptyset$ and every $n \in S$ is equivalent to $m$ ($m \sqsubseteq n \sqsubseteq m$), or $S = \emptyset$ and $m = \pi$; for a partial order this means $J(m) = \{\{m\}\}$ for $m \ne \pi$ and $J(\pi) = \{\{\pi\}, \emptyset\}$ (their Lemma 2.1 and Definition 2.11); the basic GRMs are exactly the [Kripke resource models with an inconsistent world](kripke-resource-models-with-inconsistency.md) (their Lemma 5.6). Pym, O'Hearn and Yang present the same notion in their Definitions 12 to 15; as printed there, the Sieve and Stability conditions have the orientation used here while condition (K) is stated downwards, so this page follows the consistent upward presentation of Galmiche, Méry and Pym. The models generalize the topological Kripke models on sheaves over a topological monoid, which also handle $\bot$ by an inconsistent world.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Section 2.2, Definition 2.8 (GTM), Definition 2.9 (GTI), Definition 2.10 (GRM) and the definition of validity after it.
- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 5.3, Definitions 12 to 15, Table 4, and Lemmas 16 and 17.
