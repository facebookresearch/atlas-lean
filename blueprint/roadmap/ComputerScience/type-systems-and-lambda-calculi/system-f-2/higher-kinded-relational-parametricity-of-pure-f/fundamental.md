# Fundamental theorem of higher-kinded parametricity for Fω

Let $\Gamma$ be a [term context](../scoped-pure-f-terms/ctx.md) with $m$ term variables over a
kinding context $\Delta$, $t \in \mathrm{Tm}_{\Delta,m}$ and $A \in \mathrm{Ty}^{\star}_{\Delta}$
with $\Gamma \vdash t : A$ ([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)).
Let $\rho$ assign to each type variable $\alpha_i$ of kind $\kappa_i$ in $\Delta$ an element of
$[\![\kappa_i]\!]_{\mathcal{R}}$: a [β-invariant
relation](../../system-f/binary-beta-invariant-relations/rel.md) on the [untyped term
model](../../system-f/the-existing-untyped-beta-conversion-term-model/model.md) for kind $\star$,
and a function between such interpretations for higher kinds. Let $\sigma$, $\tau$ be two
independently chosen assignments of model terms to the term variables with
$[\![\Gamma(i)]\!]_\rho(\sigma(i), \tau(i))$ for every $i < m$ ([relational
interpretation](../higher-kinded-relational-interpretation-of-f-typ/interpret.md)). Then the
[closings](../f-closing-instances-in-the-single-existing-term/close.md) are related:
$[\![A]\!]_\rho(t\{\sigma\}, t\{\tau\})$.

This is an adaptation of Reynolds' abstraction theorem (1983) and of Wadler's formulation with
related environments (1989) to Fω, with relations interpreted syntactically as β-invariant relations
on erased terms rather than in a set-theoretic semantics.

## Sources

- J. C. Reynolds, *Types, abstraction and parametric polymorphism*, in R. E. A. Mason (ed.), Information Processing 83, Proceedings of the IFIP 9th World Computer Congress, North-Holland, 1983, 513–523.
- P. Wadler, *Theorems for free!*, Proceedings of the Fourth International Conference on Functional Programming Languages and Computer Architecture (FPCA '89), ACM, 1989, 347–359.
