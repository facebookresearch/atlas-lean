# Validity of ∃∀ sentences for metric spaces and of ∀∃ sentences for normed spaces is undecidable

Validity over classes of metric spaces is undecidable already for prenex sentences with an existential block followed by a universal block, and over classes of normed spaces of a fixed dimension at least 2 already for universal-existential sentences, although the purely universal and purely existential fragments are decidable.

**Setting.** Sentences are in the two-sorted languages of metric spaces and of normed spaces described on the page on [theories of metric and normed spaces](theories-of-metric-and-normed-spaces.md), with scalars interpreted in the ordered field of real numbers. A sentence is $\forall\exists$ if it is in prenex form $\forall x_1\cdots\forall x_n\,\exists y_1\cdots\exists y_m\,\phi$ with $\phi$ quantifier-free and variables of either sort, $\exists\forall$ if the blocks are exchanged, and $\forall{\Rightarrow}\forall$ if it has the form $(\forall\mathbf x\,\phi)\Rightarrow(\forall\mathbf y\,\psi)$ with $\phi,\psi$ quantifier-free. A sentence is *valid* in a class of structures if it holds in every member.

**Theorem (Solovay, Arthan and Harrison).**

1. If $\mathcal C$ is any class of metric spaces that includes the metric space $\mathbb Z$ with $d(x,y)=|x-y|$, then the set of $\exists\forall$ sentences valid in $\mathcal C$ is undecidable (Theorem 9).
2. Let $d\in\{2,3,4,\dots\}\cup\{\infty\}$ and let $\mathcal C$ be any class of normed spaces that includes all Banach spaces of dimension $d$. Then the sets of $\exists\forall$ sentences (Corollary 44), of $\forall\exists$ sentences (Theorem 46) and of $\forall{\Rightarrow}\forall$ sentences (Theorem 47) valid in $\mathcal C$ are undecidable.

These are sharp: the set of valid $\forall\exists$ sentences of the theory of metric spaces is decidable, and so are the purely universal and the purely existential fragments of the theory of normed spaces.

## Depends on

- [The theories of metric spaces and normed spaces are not arithmetical](theories-of-metric-and-normed-spaces.md)
- [Normed vector space](../../../../Analysis/banach-spaces/normed-spaces/normed-space.md)
- [Metric on a set, as a function](../../../../ComputerScience/machine-learning/unsupervised-learning/single-linkage-hierarchical-clustering/is-metric-fn.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

All parts reduce the solvability of Diophantine equations (Hilbert's tenth problem). In the metric space $\mathbb Z$, natural numbers are definable among the scalars by a formula with few quantifiers over points, so a Diophantine equation has a solution exactly when an $\exists\forall$ sentence fails in $\mathcal C$; validity of such sentences would thus decide Hilbert's tenth problem. For normed spaces, a norm on $\mathbb R^2$ whose unit sphere is a polygon with suitably spaced extreme points lets a formula of the required quantifier shape define the natural numbers as the ratios of distances between adjacent extreme points, and the property transfers to Banach spaces of dimension $d$; the reductions then give the three fragments.

## Sources

- R. M. Solovay, R. D. Arthan and J. Harrison, "Some new results on decidability for elementary algebra and geometry", *Annals of Pure and Applied Logic* 163(12), pp. 1765–1802, 2012, doi:[10.1016/j.apal.2012.04.003](https://doi.org/10.1016/j.apal.2012.04.003); read in arXiv:0904.3482v3 ([arXiv](https://arxiv.org/abs/0904.3482v3)), whose numbering is used: the subsections on the decidability of the $\forall\exists$ fragment and the undecidability of the $\exists\forall$ fragment for metric spaces (Theorem 9), Corollary 44 and Theorems 46 and 47 for normed spaces, and the abstract for the decidable fragments.
