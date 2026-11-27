# Transitive closure logic of the infinite grid is undecidable

The theory of the infinite grid $(\omega^2, S_1, S_2)$ in first-order logic with transitive closure is undecidable already when transitive closure is applied only to binary relations, without parameters, with nesting depth two; with unnested transitive closure the theory is decidable.

**Transitive closure logic.** $\mathrm{FO(TC)}$ extends first-order logic by formulas $[\mathrm{TC}_{\bar{x},\bar{y}}\,\varphi(\bar{x},\bar{y},\bar{z})]\,\bar{s},\bar{t}$, where $\bar{x}, \bar{y}, \bar{s}, \bar{t}$ are tuples of variables of the same length $k > 0$ and $\bar{x}, \bar{y}$ are disjoint. Given values $\bar{c}$ of the parameters $\bar{z}$, it holds of $\bar{s}, \bar{t}$ iff $(\bar{s}, \bar{t})$ is in the transitive closure of the relation $\{(\bar{a}, \bar{b}) : \varphi(\bar{a}, \bar{b}, \bar{c})\}$ on $k$-tuples. $\mathrm{FO(TC)}_{(1)}$ allows only $k = 1$ (transitive closures of binary relations), and $\mathrm{FO(TC)}^l_{(1)}$ further bounds the nesting depth of $\mathrm{TC}$ operators by $l$.

**The grid.** $\mathcal{G} = (\omega^2, S_1, S_2)$ with $S_1 = \{((i,j),(i+1,j))\}$ and $S_2 = \{((i,j),(i,j+1))\}$; it is the asynchronous product of two copies of $(\omega, \mathrm{succ})$.

**Theorem (Wöhrle and Thomas).** The $\mathrm{FO(TC)}^2_{(1)}$-theory of $\mathcal{G}$, that is, the set of $\mathrm{FO(TC)}^2_{(1)}$ sentences true in $\mathcal{G}$, is undecidable (Theorem 4.2). This holds already for sentences whose $\mathrm{TC}$ operators use no parameters.

In contrast, the $\mathrm{FO(TC)}^1_{(1)}$-theory of $\mathcal{G}$, parameters allowed, is decidable (Theorem 4.3), and the $\mathrm{FO(TC)}_{(1)}$-theory of each component $(\omega, \mathrm{succ})$ is decidable, being interpretable in its monadic second-order theory.

## Depends on

- [Formulas of first-order logic with transitive closure](../../../TheoryOfComputation/descriptive-complexity/transitive-closure-logic-and-nl/tcfo.md)
- [Complete theory of a first-order structure](../../first-order-logic/theory-of-structure.md)

## Proof depends on

- [Tarski's undefinability theorem](../../proof-theory/g-del-s-incompleteness-theorems/tarski-s-undefinability-theorem.md)

## Expansion

Points of $\mathcal{G}$ code pairs of naturals, and $\mathrm{FO(TC)}_{(1)}$ over $\mathcal{G}$ corresponds to $\mathrm{FO(TC)}_{(2)}$ over $(\omega, \mathrm{succ})$ (Lemma 4.1). Addition is $a + b = c$ iff $(0, a)$ reaches $(b, c)$ by simultaneous successor steps. Since $xy = ((x+y)^2 - x^2 - y^2)/2$, multiplication reduces to squaring, and $x^2 = \sum_{i<x} (2i+1)$ is defined by a second, nested transitive closure. Thus first-order arithmetic $\mathrm{FO}(\omega, +, \times)$, whose theory is undecidable, is interpreted without parameters. The decidable case reduces to Presburger arithmetic. The paper's compositional theorem shows that $\mathrm{FO}$ with reachability predicates is preserved by finitely synchronized products, so the grid result marks the limit of that theorem.

## Sources

- Stefan Wöhrle and Wolfgang Thomas, "Model checking synchronized products of infinite transition systems", *Logical Methods in Computer Science* 3(4):5, 2007, doi:10.2168/LMCS-3(4:5)2007; read as arXiv:0710.5659v2, <https://arxiv.org/abs/0710.5659v2>: Section 2.2 (transitive closure logic and its fragments $\mathrm{FO(TC)}^l_{(k)}$), Theorems 4.2 and 4.3 and Section 4 of arXiv:0710.5659v2.
