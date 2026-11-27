# Beth's definability theorem

Let $T$ be a theory in a first-order language $L$ and $R$ an $n$-ary relation symbol of $L$. Say that $T$ *implicitly defines* $R$ if for all models $M$ and $N$ of $T$, every bijection $e : M \to N$ that preserves every function symbol and every relation symbol other than $R$ also preserves $R$. Then there is a formula $\theta(x_1, \dots, x_n)$ of $L$ in which $R$ does not occur such that every model of $T$ satisfies $\forall \bar x\, (R(\bar x) \leftrightarrow \theta(\bar x))$: $T$ *explicitly defines* $R$. The converse is immediate. Implicit definability is a property of the theory, not of one model: a relation determined uniquely in a single model need not be implicitly defined by that model's theory.

## Sources

- S. R. Buss, "An introduction to proof theory", in S. R. Buss (ed.), *Handbook of Proof Theory*, Elsevier, 1998, Chapter I, Section 2.5.6, Beth's definability theorem, its definitions and the example of multiplication over addition, <https://www.math.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf>
- E. W. Beth, "On Padoa's method in the theory of definition", *Indagationes Mathematicae* 15:330–339, 1953
