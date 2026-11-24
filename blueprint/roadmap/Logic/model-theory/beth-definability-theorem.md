# Beth's definability theorem

Let $P$ and $P'$ be predicate symbols of the same arity $n$, let $\Gamma(P)$ be a set of first-order sentences in which $P'$ does not occur, and let $\Gamma(P')$ be the result of replacing every occurrence of $P$ by $P'$. Say that $\Gamma(P)$ *implicitly defines* $P$ if $\Gamma(P) \cup \Gamma(P') \models \forall \bar x\, (P(\bar x) \leftrightarrow P'(\bar x))$, and that it *explicitly defines* $P$ if there is a formula $A(\bar x)$ in which neither $P$ nor $P'$ occurs such that $\Gamma(P) \models \forall \bar x\, (A(\bar x) \leftrightarrow P(\bar x))$. Then $\Gamma(P)$ implicitly defines $P$ if and only if it explicitly defines $P$. Implicit definability is a property of the theory, not of one model: a predicate determined uniquely in a single model need not be implicitly defined by that model's theory.

## Proof depends on

- [Craig interpolation for first-order logic](../proof-theory/craig-interpolation-for-first-order-logic.md)

## Sources

- S. R. Buss, "An introduction to proof theory", in S. R. Buss (ed.), *Handbook of Proof Theory*, Elsevier, 1998, Chapter I, Section 2.5.6, Beth's definability theorem, its definitions and the example of multiplication over addition, <https://www.math.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf>
- E. W. Beth, "On Padoa's method in the theory of definition", *Indagationes Mathematicae* 15:330–339, 1953
