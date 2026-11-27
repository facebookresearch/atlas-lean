# Equality in extensional type theory and in the free locally cartesian closed category is undecidable

Judgmental equality in Martin-Löf type theory with extensional identity types, dependent function types and one base type is undecidable, and hence so is equality of arrows in the free locally cartesian closed category on one object; type inhabitation is undecidable with intensional or extensional identity types.

**Setting (Castellan, Clairambault and Dybjer).** Consider Martin-Löf type theory with a base type $o$, dependent function types $\Pi$ and identity types $\mathrm{I}(A, a, b)$, either *intensional* or *extensional*; with extensional identity types, an inhabitant of $\mathrm{I}(A, a, b)$ in a context $\Gamma$ forces the judgment $\Gamma \vdash a = b : A$. *Type inhabitation* asks, given a context $\Gamma$ and a type $A$ in it, whether some term $t$ has $\Gamma \vdash t : A$; *judgmental equality* asks, given $\Gamma \vdash a : A$ and $\Gamma \vdash b : A$, whether $\Gamma \vdash a = b : A$ is derivable. A *locally cartesian closed category* (lccc) is a category with finite limits in which every slice category is cartesian closed; the *bifree* lccc on one object is bi-initial in the 2-category of lcccs with a chosen object.

**Theorem (Castellan, Clairambault and Dybjer).**

1. Type inhabitation in Martin-Löf type theory with intensional or extensional identity types, $\Pi$-types and a base type is undecidable.
2. Judgmental equality in Martin-Löf type theory with extensional identity types, $\Pi$-types and a base type is undecidable; this also holds when a unit type and $\Sigma$-types are added.
3. Equality of arrows in the bifree locally cartesian closed category on one object is undecidable.

The authors show that the category of contexts of the type theory with extensional identity types, a unit type, $\Sigma$-types and $\Pi$-types is the bifree lccc on one object, which gives clause 3 from clause 2. The same construction proves the folklore result that judgmental equality is undecidable for extensional type theory with $\Pi$-types and one universe.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

All clauses reduce from convertibility of closed terms of combinatory logic. In the context $\Gamma_{CL}$ declaring $o$, constants $k, s : o$, an application operation $\cdot : o \to o \to o$ and axioms $\Pi x\, y : o.\ \mathrm{I}(o, k \cdot x \cdot y, x)$ and $\Pi x\, y\, z : o.\ \mathrm{I}(o, s \cdot x \cdot y \cdot z, x \cdot z \cdot (y \cdot z))$, the type $\mathrm{I}(o, M, M')$ is inhabited exactly when the closed combinatory terms $M$ and $M'$ are convertible: convertibility can be derived inside the theory, and conversely a model interprets $o$ as the set of combinatory terms modulo convertibility. With extensional identity types this inhabitation is equivalent to the judgment $\Gamma_{CL} \vdash M = M' : o$. A good expansion adds and links a page for the undecidability of convertibility in combinatory logic and for the biequivalence between lcccs and the corresponding fragment of extensional type theory.

## Sources

- Simon Castellan, Pierre Clairambault and Peter Dybjer, *Undecidability of Equality in the Free Locally Cartesian Closed Category (Extended version)*, Logical Methods in Computer Science 13(4), 2017, https://doi.org/10.23638/LMCS-13(4:22)2017; the undecidability theorems of the introduction and the bifreeness theorem at the end of the paper, read in arXiv:1504.03995v3. Locators in arXiv:1504.03995v3: Theorems 2.1, 2.2, 2.3 and 4.25.
