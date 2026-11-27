# Some computable interval map has a Π₁-complete attractor and a non-computable physical measure

There is a computable map of the unit interval whose attractor, a transitive metric and statistical attractor inside a Cantor set, is a $\Pi_1$-complete closed set, so that neither the attractor nor the unique physical measure it supports is computable.

Let $f\colon [0,1] \to [0,1]$ be a map and $\lambda$ Lebesgue measure. For $x \in [0,1]$ let $\omega(x)$ be its $\omega$-limit set, and for a closed set $A$ let $\rho(A) = \{x : \omega(x) \subseteq A\}$ be its topological basin.

- $A$ is a *metric attractor* if $\rho(A)$ has full measure and no strictly smaller closed set $A' \subset A$ has $\rho(A')$ of positive measure.
- $A$ is a *statistical (physical) attractor* if there is a unique invariant probability measure $\mu$ with $\operatorname{supp}\mu = A$ and $\mu = \lim_{n\to\infty} \frac{1}{n}\sum_{i<n} \delta_{f^i(x)}$ (weak-$*$ limit) for $\lambda$-almost every $x$; such a $\mu$ is called a *physical measure*.
- $A$ is *transitive* if some point of $A$ has a dense orbit in $A$.
- For a fixed enumeration $(B_i)$ of the open balls with rational centers and radii, the *outer collection* of a compact $K$ is $\{i : \overline{B_i} \cap K = \emptyset\}$. $K$ is $\Pi_1$ if its outer collection is computably enumerable, and *$\Pi_1$-complete* if moreover, given an enumeration of the outer collection of $K$, one can enumerate the outer collection of any other $\Pi_1$ compact set. A $\Pi_1$-complete set is not computable.
- $f$ is *computable* if a Turing machine with an oracle for $x$ outputs $f(x)$ to any requested precision.

**Theorem (Rojas–Sablik).** There exist a computable map $f\colon [0,1] \to [0,1]$ and an invariant set $\mathcal{A} \subset [0,1]$ such that $\mathcal{A}$ is $\Pi_1$-complete and $\mathcal{A}$ is a transitive metric and statistical attractor for $f$. In particular, $f$ has a unique physical measure, which is not computable (Corollary 1 of the source).

The same method gives a computable map $f\colon [0,1] \to [0,1]$ with a $\Pi_2$-complete metric attractor (Corollary 2), whose statistical attractor is then the single point $\{0\}$. These lower bounds are complemented by general upper bounds on the complexity of metric, topological and statistical attractors of computable maps (Theorem 1).

## Depends on

- [Lebesgue measure on the real line](../../../MeasureTheory/lebesgue-measure/lebesgue-measure-on-euclidean-spaces/lebesgue-measure-on-the-real-line/lebesgue-measure.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

First a computable map $T$ of the Cantor space $\{0,1\}^{\mathbb{N}}$ is built with an invariant closed set $A$ that is $\Pi_1$-complete, is the topological and metric attractor of $T$, carries a topologically mixing shift dynamics of positive entropy, attracts every point, and is the statistical attractor for every shift-ergodic reference measure of full support (Theorem 2). Completeness comes from encoding the complement of the halting set $\{i : M_i \text{ halts on the empty input}\}$, which is $\Pi_1$-complete, into which patterns are forbidden in $A$. Then $T$ is transported to the interval (Theorem 6): one builds a computable fat Cantor set $\mathcal{C} \subset [0,1]$ of Lebesgue measure $1/2$, a computable homeomorphism $\phi\colon \{0,1\}^{\mathbb{N}} \to \mathcal{C}$ and a computable map $f$ of $[0,1]$ preserving $\mathcal{C}$, conjugate to $T$ on $\mathcal{C}$ through $\phi$, such that Lebesgue almost every orbit accumulates only on $\mathcal{C}$ and metric or statistical attractors of $T$ are carried to attractors of $f$ of the same type. Applying this to $T$ gives $f$ and $\mathcal{A} = \phi(A)$. The construction of $T$ and the embedding theorem have no pages.

## Sources

- C. Rojas and M. Sablik, "On the algorithmic descriptive complexity of attractors in topological dynamics", Ergodic Theory and Dynamical Systems 45 (2025), no. 8, 2533–2560, https://doi.org/10.1017/etds.2024.135; read in arXiv:2311.15234v2 (Definitions 1 to 5, Theorems 1, 2 and 6 and Corollaries 1 and 2 of arXiv:2311.15234v2).
