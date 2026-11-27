# Guarded fragment of first-order logic

The guarded fragment restricts first-order quantification to the bounded forms $\forall \bar{y}\,(G \to \varphi)$ and $\exists \bar{y}\,(G \wedge \varphi)$, where the guard $G$ is an atom containing all free variables of $\varphi$; its extensions declare some binary relations transitive or functional.

**Definition.** Over a relational signature with equality, the *guarded fragment* $\mathrm{GF}$ is the least set of formulas that contains all atomic formulas, is closed under $\neg$, $\vee$, $\wedge$ and $\to$, and contains $\forall \bar{y}\,(G \to \varphi)$ and $\exists \bar{y}\,(G \wedge \varphi)$ whenever $\varphi \in \mathrm{GF}$ and $G$ is an atomic formula, the *guard*, containing all free variables of $\varphi$. For $k \geq 1$, $\mathrm{GF}^k$ is the set of $\mathrm{GF}$ formulas in which only $k$ distinct variables occur; for $k = 2$ the guarded quantifiers have the form $\forall u\,(G \to \varphi)$ and $\exists u\,(G \wedge \varphi)$ with $u \in \{x, y\}$ free in $G$, and equality may serve as a guard.

**Special relations.** In extensions of $\mathrm{GF}$ (or $\mathrm{GF}^k$) by *transitive relations*, some binary relation symbols are distinguished and required to denote transitive relations; their occurrence may be unrestricted, or, in $\mathrm{GF}$ *with transitive guards*, restricted to guard positions. In an extension by a *functional relation*, a distinguished binary relation symbol is required to denote a partial function. Satisfiability (respectively finite satisfiability) asks whether a sentence has a model (a finite model) in which the distinguished symbols are interpreted as required.

## Depends on

None.

## Proof depends on

None.

## Expansion

The guarded fragment was introduced by Andréka, van Benthem and Németi as a first-order counterpart of modal logics. It is decidable, in 2EXPTIME (Grädel), and has the finite model property, interpolation and invariance under guarded bisimulation. The transitivity axiom $\forall xyz\,(xTy \wedge yTz \to xTz)$ is not guarded, which is why transitivity is added as a semantic constraint.

## Sources

- Y. Kazakov and H. de Nivelle, "A resolution decision procedure for the guarded fragment with transitive guards", in *Automated Reasoning (IJCAR 2004)*, Lecture Notes in Computer Science 3097, Springer, 2004, pp. 122–136, doi:10.1007/978-3-540-25984-8_7; read in the author's open-access copy at <https://ora.ox.ac.uk/objects/uuid:4910c16d-da7c-4544-b0ef-f793db629cd2/files/m3bec760d1bdf839ce335fa727ff3fd30>: Section 1.
- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), article 8, 2018, doi:10.1145/3174805; read as arXiv:1611.03267v3, <https://arxiv.org/abs/1611.03267v3>: Section 2 (the definition of $\mathrm{GF}^2$ and its extensions) and Section 1.
