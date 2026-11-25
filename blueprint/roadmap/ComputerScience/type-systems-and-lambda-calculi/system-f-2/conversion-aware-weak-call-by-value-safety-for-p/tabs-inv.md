# Inversion of Fω type-lambda typing up to conversion

Let $\Gamma$ be a term context over $\Delta$, $\kappa$ a kind, $T \in \mathrm{Ty}^{\star}_{\Delta}$
and $b \in \mathrm{Tm}_{\kappa \cdot \Delta,m}$ with $\Gamma \vdash \Lambda_\kappa b : T$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)). Then there is $B \in
\mathrm{Ty}^{\star}_{\kappa \cdot \Delta}$ with $\Gamma^{\uparrow} \vdash b : B$ (the context
weakened by the successor renaming) and $\forall_\kappa B \equiv_\beta T$ ([type
β-conversion](../proved-type-beta-conversion-for-pure-f/conv.md)).
