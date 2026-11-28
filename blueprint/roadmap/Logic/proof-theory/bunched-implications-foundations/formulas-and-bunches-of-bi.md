# Formulas and bunches of BI

The propositions of the logic of bunched implications BI are defined over the additive connectives of intuitionistic logic together with the multiplicative unit $\mathrm{I}$, conjunction $\ast$ and implication $\mathrel{-\!\!\ast}$; the antecedent of a BI judgement is a bunch, a finite tree built with two context-forming operations.

Fix a countable set $L$ of propositional letters. The set $\mathcal{P}(L)$ of BI propositions over $L$ is given by

$$
\varphi ::= p \mid \mathrm{I} \mid \varphi \ast \varphi \mid \varphi \mathrel{-\!\!\ast} \varphi \mid \top \mid \bot \mid \varphi \wedge \varphi \mid \varphi \to \varphi \mid \varphi \vee \varphi \qquad (p \in L).
$$

The additive connectives $\top, \bot, \wedge, \to, \vee$ are those of intuitionistic propositional logic; the multiplicative connectives $\mathrm{I}, \ast, \mathrel{-\!\!\ast}$ are those of multiplicative intuitionistic linear logic. BI contains no multiplicative disjunction.

*Bunches* are given by the grammar

$$
\Gamma ::= \varphi \mid \emptyset_a \mid \Gamma ; \Gamma \mid \emptyset_m \mid \Gamma , \Gamma ,
$$

where $\varphi$ ranges over propositions, ";" is *additive combination* with unit $\emptyset_a$ and "," is *multiplicative combination* with unit $\emptyset_m$. $\Gamma(\Delta)$ denotes a bunch with a distinguished sub-bunch occurrence $\Delta$ (a subtree), and $\Gamma(\Delta')$ the bunch obtained by replacing that occurrence by $\Delta'$.

*Coherent equivalence* $\equiv$ is the least equivalence relation on bunches such that

1. ";" is associative and commutative with unit $\emptyset_a$, up to $\equiv$;
2. "," is associative and commutative with unit $\emptyset_m$, up to $\equiv$;
3. if $\Delta \equiv \Delta'$ then $\Gamma(\Delta) \equiv \Gamma(\Delta')$.

Neither combination distributes over the other: for example $\varphi ; (\psi , \chi)$ and $(\varphi ; \psi) , (\varphi ; \chi)$ are not coherently equivalent. A *judgement* (sequent) has the form $\Gamma \vdash \varphi$ with $\Gamma$ a bunch and $\varphi$ a proposition.

The formula $\Phi_\Gamma$ of a bunch $\Gamma$ is obtained by replacing each ";" by $\wedge$, each "," by $\ast$, each $\emptyset_a$ by $\top$ and each $\emptyset_m$ by $\mathrm{I}$, with association following the tree structure of $\Gamma$; semantics of judgements is defined through $\Phi_\Gamma$.

## Depends on

None.

## Proof depends on

None.

## Expansion

No prerequisite is missing: the definition is purely syntactic. O'Hearn and Pym write $1$ for $\top$ and $\{\}_a$, $\{\}_m$ for $\emptyset_a$, $\emptyset_m$; the notation here follows Galmiche, Méry and Pym. Bunches are trees taken up to $\equiv$ rather than nested multisets, so that the two implications can be introduced by extending a bunch with ";" or with ",". Later pages use the formula $\Phi_\Gamma$ to define validity of a judgement in a model.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2 (paragraphs "Connectives", "Bunches", "Coherent equivalence" and "Judgements").
- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Definition 2.1 (propositions), Definition 2.2 (bunches), and the definition of $\Phi_\Gamma$ after Definition 2.5.
