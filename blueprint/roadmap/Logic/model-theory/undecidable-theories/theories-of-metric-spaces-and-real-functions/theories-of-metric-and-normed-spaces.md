# The theories of metric spaces and normed spaces are not arithmetical

In a two-sorted language with real scalars, the first-order theories of metric spaces, of normed spaces of any fixed dimension at least 2 and of Banach spaces interpret second-order arithmetic, so none of them is decidable, recursively axiomatizable or even arithmetical.

**Languages.** The structures are two-sorted, with a sort of scalars, interpreted as the ordered field of real numbers with $+$, $\cdot$, $<$, $0$, $1$, and a sort of points or vectors. The language $\mathcal L_M$ of metric spaces adds a distance function $d$ from pairs of points to scalars; the language $\mathcal L_N$ of normed spaces has the real vector-space operations (vector addition, zero, scalar multiplication) and a norm from vectors to scalars. For a class of structures, its *theory* is the set of sentences true in every member. $\mathrm{MS}$ is the theory of metric spaces; $\mathrm{NS}_n$, $\mathrm{NS}_{\mathrm{fin}}$, $\mathrm{NS}_\infty$ and $\mathrm{NS}$ are the theories of normed spaces of dimension $n$, of finite dimension, of infinite dimension and of arbitrary dimension, and $\mathrm{BS}_\infty$, $\mathrm{BS}$ the corresponding theories of Banach spaces. The *additive* versions forbid multiplication of scalars.

**Theorem (Solovay, Arthan and Harrison).** There is a primitive recursive reduction of the set of truths of second-order arithmetic to $\mathrm{MS}$, and also to the additive theory of metric spaces (Theorems 4 and 5 of the source), and to each of $\mathrm{BS}$, $\mathrm{BS}_\infty$, $\mathrm{NS}$, $\mathrm{NS}_n$ for $n\ge2$, $\mathrm{NS}_{\mathrm{fin}}$ and $\mathrm{NS}_\infty$ (Theorem 13).

The source also determines the exact degrees. $\mathrm{NS}_{\mathrm{fin}}$ and each $\mathrm{NS}_n$ reduce primitive recursively to second-order arithmetic (Theorem 21), so $\mathrm{NS}_{\mathrm{fin}}$ and $\mathrm{NS}_n$ for $n\ge2$ have the same many-one degree as the set of truths of second-order arithmetic (Corollary 22, with Theorem 17); and $\mathrm{NS}$, $\mathrm{BS}$, $\mathrm{NS}_\infty$ and $\mathrm{BS}_\infty$ are many-one equivalent to the set of true $\Pi^2_1$ sentences of third-order arithmetic (Theorems 23 and 25 and Corollary 26).

In particular these theories are not arithmetical, hence not recursively enumerable or recursively axiomatizable. By contrast, the theory of $1$-dimensional normed spaces and the theories of real vector spaces, inner product spaces and Hilbert spaces are decidable.

## Depends on

- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Normed vector space](../../../../Analysis/banach-spaces/normed-spaces/normed-space.md)
- [Metric on a set, as a function](../../../../ComputerScience/machine-learning/unsupervised-learning/single-linkage-hierarchical-clustering/is-metric-fn.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

None.

## Expansion

The basic tool (Theorems 2 and 3 of the source) is that second-order arithmetic reduces to the theory of any structure over the real field in which the natural numbers are first-order definable as a set of scalars, with a variant for languages whose scalars carry only addition, order and $1$. In the metric space $\mathbb Z$ with $d(x,y)=|x-y|$, the formula $\exists a\,\exists b\;d(a,b)=x$ defines the natural numbers among the scalars, which gives part 1. For normed spaces of dimension at least $2$, a construction with a suitably chosen norm makes $\mathbb N$ definable in some member of each class, which gives part 2. The upper bounds in parts 3 and 4 code finite-dimensional, respectively arbitrary, normed spaces by reals, respectively by sets of reals, in second-order, respectively third-order, arithmetic. A good expansion links pages for the definability lemma and for the undecidability of second-order arithmetic; neither has a page yet.

## Sources

- R. M. Solovay, R. D. Arthan and J. Harrison, "Some new results on decidability for elementary algebra and geometry", *Annals of Pure and Applied Logic* 163(12), pp. 1765–1802, 2012, doi:[10.1016/j.apal.2012.04.003](https://doi.org/10.1016/j.apal.2012.04.003); read in arXiv:0904.3482v3 ([arXiv](https://arxiv.org/abs/0904.3482v3)), whose numbering is used: the languages of the section on languages, Theorems 2 and 3 (reductions of second-order arithmetic), Theorems 4 and 5 (metric spaces), Theorem 13 (normed and Banach spaces), Theorems 17, 21, 23 and 25 and Corollaries 22 and 26 (degrees), and the introduction for the decidable cases.
