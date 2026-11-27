# Universal sentences about one continuous or monotone real function are undecidable

For first-order sentences about a single unknown real function, with order and equality but no arithmetic, truth for all continuous functions is undecidable already for separated sentences with three quantifier alternations, and truth for all monotone functions with finitely many flat pieces is undecidable as well.

**The theory.** Let $F$ be a family of functions from $\mathbb R$ to $\mathbb R$, or from $I=[0,1]$ to $I$. The sentences considered are $(\forall f\in F)\,\varphi$, where $\varphi$ is a first-order sentence built from variables ranging over $\mathbb R$ (respectively $I$), terms $x$ and $f(x)$ for a single unary function symbol $f$, the comparators $<$, $>$, $=$, Boolean connectives and quantifiers over real numbers; no arithmetic operations occur. A prenex sentence is $\Sigma_k$ or $\Pi_k$ if its prefix has $k$ blocks of quantifiers starting with $\exists$, respectively $\forall$. A quantifier-free formula is *separated* if no term $f(f(x))$ occurs and its variables split into domain variables (the arguments of $f$) and range variables (compared with values of $f$), with no comparison between a domain variable and a range variable; it is *weak* if, moreover, the order is never used to compare elements of the range. A prenex sentence is separated or weak when its matrix is.

**Theorem (Friedman and Seress).** The set of sentences $\varphi$ with $(\forall f\in F)\,\varphi$ true is undecidable in each of the following cases:

1. $F$ consists of all continuous functions from $\mathbb R$ to $\mathbb R$, or from $I$ to $I$, and $\varphi$ ranges over separated $\Sigma_4$ sentences;
2. $F$ is any family of functions from $\mathbb R$ to $\mathbb R$ containing all analytic functions, or any family of functions from $I$ to $I$ containing all polynomials, and $\varphi$ ranges over weak separated $\Sigma_4$ sentences;
3. $F$ is any family of functions from $\mathbb R$ to $\mathbb R$, or from $I$ to $I$, containing all nondecreasing $C^\infty$ functions that are constant on finitely many intervals, and $\varphi$ ranges over all sentences;
4. $F$ consists of the strictly monotone functions from $\mathbb R$ to $\mathbb R$ that are left-continuous and have finitely many discontinuities.

By contrast, for the continuous, differentiable, $C^\infty$ and analytic functions, the $\Sigma_1$ and $\Pi_1$ sentences and the separated $\Pi_2$ sentences are decidable; all sentences are decidable for the continuous strictly monotone functions; and for the polynomials truth is co-recursively enumerable.

## Depends on

None.

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Parts 1 and 2 reduce from finite graph theory: the validity problem for $\Sigma_2$ sentences about finite symmetric irreflexive relations is undecidable (Gurevich), and an algorithm maps each such sentence $\psi$ to a separated $\Sigma_4$ sentence $\varphi$ such that $\psi$ holds in all finite graphs exactly when $(\forall f\in F)\,\varphi$ holds for the continuous functions. Parts 3 and 4 encode Turing machines: for a machine $T$ started on the empty tape one builds a sentence $\varphi(T)$ that some function with finitely many constant intervals satisfies exactly when $T$ halts. A good expansion links a page for Gurevich's undecidability of $\Sigma_2$ validity over finite graphs, which has no page yet.

## Sources

- H. Friedman and Á. Seress, "Decidability in elementary analysis. I", *Advances in Mathematics* 76(1), pp. 94–115, 1989, doi:[10.1016/0001-8708(89)90044-3](https://doi.org/10.1016/0001-8708(89)90044-3): Section 4, Theorem 4.2, for parts 1 and 2 (not read here; locator as given by the survey).
- H. Friedman and Á. Seress, "Decidability in elementary analysis. II", *Advances in Mathematics* 79(1), pp. 1–17, 1990, doi:[10.1016/0001-8708(90)90056-S](https://doi.org/10.1016/0001-8708(90)90056-S): Section 1 for parts 3 and 4, Section 4, Theorem 4.7, for the polynomials (not read here; locators as given by the survey).
- D. Cantone, E. G. Omodeo and G. T. Spartà, "Solvable (and unsolvable) cases of the decision problem for fragments of analysis", *Rendiconti dell'Istituto di Matematica dell'Università di Trieste* 44, pp. 313–348, 2012, a refereed survey and the copy read: Definition 1.8, Propositions 1.6, 1.11, 1.13 and 1.15, and the reductions in Subsections 1.2 and 1.3 (its footnote notes that the source for part 4 treats only functions on $\mathbb R$).
