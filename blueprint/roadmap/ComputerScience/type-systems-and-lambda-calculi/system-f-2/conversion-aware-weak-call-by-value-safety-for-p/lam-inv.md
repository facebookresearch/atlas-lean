# Inversion of Fω lambda typing up to conversion

Let $\Gamma$ be a term context over $\Delta$, $A, T \in \mathrm{Ty}^{\star}_{\Delta}$ and $b \in
\mathrm{Tm}_{\Delta,m+1}$ with $\Gamma \vdash \lambda A.\,b : T$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)). Then there is $B \in
\mathrm{Ty}^{\star}_{\Delta}$ with $A \cdot \Gamma \vdash b : B$ and $A \to B \equiv_\beta T$ ([type
β-conversion](../proved-type-beta-conversion-for-pure-f/conv.md)).
