# Emptiness of extremely expansive two-dimensional SFTs is undecidable

No algorithm decides whether a two-dimensional subshift of finite type is empty, even when it is promised to be either empty or extremely expansive, that is, to have exactly one non-expansive direction.

Let $X \subseteq A^{\mathbb{Z}^2}$ be a two-dimensional subshift. For a slope $l \in \mathbb{R} \cup \{\infty\}$ let $\overline{l} \subset \mathbb{R}^2$ be the line through the origin with slope $l$. The direction $l$ is *expansive* for $X$ if there is a bounded set $V \subset \mathbb{R}^2$ such that, for all $x, y \in X$,

$$
x|_{(\overline{l} + V) \cap \mathbb{Z}^2} = y|_{(\overline{l} + V) \cap \mathbb{Z}^2} \implies x = y ,
$$

so that every configuration is determined by its restriction to a strip of bounded width along $\overline{l}$; otherwise $l$ is *non-expansive*. Let $\mathrm{NE}(X)$ be the set of non-expansive directions. By a theorem of Boyle and Lind, $\mathrm{NE}(X)$ is closed, and it is empty exactly when $X$ is finite; $X$ is *extremely expansive* if $\mathrm{NE}(X)$ has exactly one element.

**Theorem.** It is undecidable whether an extremely expansive two-dimensional SFT is empty (Theorem 47 of the source; Theorem 2 in its overview). More precisely, there is no algorithm that, given a finite set of forbidden patterns defining a two-dimensional SFT $X$ that is either empty or extremely expansive, decides whether $X = \emptyset$.

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof uses a universal self-simulating construction built from reversible partial cellular automata: a hierarchy of SFTs in which each level simulates the next, with the simulation parameters chosen so that every non-empty level has a single non-expansive direction. Given a Turing machine $M$, the construction is fed the sequence of finite permutations that are defined at step $n$ exactly when $M$ has not halted within $n$ steps on the empty input. The resulting SFT is non-empty exactly when $M$ never halts, and when it is non-empty it is extremely expansive. Hence the set of forbidden-pattern sets defining empty SFTs and the set defining non-empty extremely expansive SFTs are not recursively separable, which is the statement. The same construction yields an aperiodic extremely expansive two-dimensional SFT (Theorem 1 of the overview), and every effective Medvedev degree contains an extremely expansive two-dimensional SFT.

## Sources

- C. Zinoviadis, *Hierarchy and expansiveness in two-dimensional subshifts of finite type*, doctoral dissertation, University of Turku, 2016, https://www.utupub.fi/handle/10024/120249; read in arXiv:1603.05464v1 (Theorems 1 and 2 of the historical overview and Theorem 47 in the section "Domino problem" of the chapter "Infinite hierarchies" of arXiv:1603.05464v1; the definition of expansive directions and Proposition 9, after M. Boyle and D. Lind, in the chapter "Preliminaries").
