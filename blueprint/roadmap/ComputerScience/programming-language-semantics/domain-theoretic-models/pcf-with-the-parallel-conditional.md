# PCF with the parallel conditional

Plotkin's PCF has ground types $o$ (truth values) and $\iota$ (natural numbers) and function types $\sigma \to \tau$; its constants are $\mathit{tt}$, $\mathit{ff}$, the numerals
$k_n$, successor $(+1)$, predecessor $(-1)$, the zero test $Z$, the sequential conditionals $\supset_\sigma$ at ground types $\sigma$, and fixed-point combinators $Y_\sigma$
at every type. A *program* is a closed term of ground type, evaluated by a deterministic call-by-name reduction $\to$; $\mathrm{Eval}(M) = c$ if $M \to^* c$ for a constant $c$.

**The parallel conditional.** PCF with parallel facilities, $\mathcal{L}_{PA}$, adds constants $:\supset_\sigma\ : o \to \sigma \to \sigma \to \sigma$ for ground $\sigma$, with reductions
$:\supset\, \mathit{tt}\, M\, N \to M$, $:\supset\, \mathit{ff}\, M\, N \to N$, and $:\supset\, L\, c\, c \to c$ for every constant $c$, together with reduction inside any
of the three arguments. Reduction is no longer deterministic, but it is Church–Rosser, so $\mathrm{Eval}_{PA}$ is well defined. The
sequential conditional and parallel or ($V = \lambda p q.\, :\supset\, p\, \mathit{tt}\, q$) are definable.

**The standard model.** Types denote the domains $D_o = \{\bot, \mathit{tt}, \mathit{ff}\}$ and $D_\iota = \{\bot, 0, 1, \dots\}$, flat, and $D_{\sigma \to \tau} = [D_\sigma \to D_\tau]$, the
continuous functions ordered pointwise. $Y_\sigma$ denotes the least-fixed-point operator, and $:\supset$ denotes the function with
$:\supset(p)(x)(y) = x$ if $p = \mathit{tt}$, $= y$ if $p = \mathit{ff}$, $= x$ if $p = \bot$ and $x = y$, and $= \bot$ if $p = \bot$ and $x \ne y$. Write $\mathcal{A}_{PA}[\![M]\!]$ for the
denotation of a term in this model.

**Operational preorder.** For terms $M$, $N$ of the same type, $M \sqsubseteq_{PA} N$ if for every context $C$ such that $C[M]$ and $C[N]$ are programs,
$\mathrm{Eval}_{PA}(C[M]) = c$ implies $\mathrm{Eval}_{PA}(C[N]) = c$; and $M \simeq_{PA} N$ if both hold. This is the same kind of preorder as
[contextual approximation](../pcf-and-computational-adequacy/ctx-approx.md) for the sequential PCF of that page, but that language differs: it has the single
ground type of natural numbers, and its predecessor of zero is zero, whereas here $(-1)\, k_0$ has no value.

## Depends on

- [Least fixed point of a Scott-continuous map](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp.md)

## Background

- [Contextual approximation in PCF](../pcf-and-computational-adequacy/ctx-approx.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 2 (the language and the standard model), Section 3 (operational semantics, Theorem 3.1), Section 4 (operational preorder and equivalence) and the definition of $\mathcal{L}_{PA}$, its reduction rules and $\mathcal{A}_{PA}$ on pages 236–237.
