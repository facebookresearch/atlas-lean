# Two-variable intuitionistic logics valid in all infinite fans are undecidable

Every set of two-variable intuitionistic formulas that contains the two-variable fragment of intuitionistic predicate logic and holds in all infinite fans, Kripke models made of a root below countably many maximal points with a common infinite domain, is undecidable.

**Theorem (Kontchakov, Kurucz and Zakharyaschev).** Let $\mathbf{QInt}(2)$ be the set of formulas of [$\mathbf{QInt}$](quantified-intuitionistic-logic-qint.md), without function symbols, constants or equality, that contain only two individual variables (bound or free). Call a first-order intuitionistic Kripke model an *infinite fan* if its frame is a countably infinite set $\{v\} \cup V$ ordered by the reflexive closure of $\{v\} \times V$, a root $v$ below the maximal points of $V$, and every point has the same countably infinite domain. Then every set $\Gamma$ of two-variable formulas with $\mathbf{QInt}(2) \subseteq \Gamma$ all of whose formulas are true in all infinite fans is undecidable.

The case $\Gamma = \mathbf{QInt}(2)$ is Theorem 1 of the source: the two-variable fragment of intuitionistic predicate logic is undecidable. That case is also a consequence of the undecidability of the [positive two-variable fragment with one monadic letter](positive-two-variable-intuitionistic-logic-with.md) (Rybakov and Shkatov), whose proof starts from this reduction. By contrast, the two-variable fragment of classical first-order logic is decidable (Mortimer), and the one-variable fragment of $\mathbf{QInt}$ is decidable (Bull; Mints; Ono). According to Rybakov and Shkatov, the reduction uses two binary and infinitely many monadic predicate symbols.

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the $\mathbb{N} \times \mathbb{N}$ tiling problem. Tilings are easy to encode in three-variable classical logic; the observation behind the reduction is that the third variable can be used only as a "stack" for substitutions, and in intuitionistic logic this use can be simulated with two variables and the Kripke structure. A formula $\varphi_T$ is built from a finite set $T$ of tile types such that $\varphi_T \notin \mathbf{QInt}(2)$ iff $T$ tiles the quadrant, and a tiling yields a countermodel that is an infinite fan; so the same formulas separate any $\Gamma$ as in the theorem from the non-tileable instances.

## Sources

- R. Kontchakov, A. Kurucz and M. Zakharyaschev, "Undecidability of first-order intuitionistic and modal logics with two variables", *Bulletin of Symbolic Logic* 11(3):428–438, 2005, doi:10.2178/bsl/1122038996; read in the authors' open-access copy at <https://kuag19.github.io/homepage/expfo.pdf>: Section 2 (intuitionistic Kripke models, the definition of $\mathbf{QInt}(2)$, Theorem 1 with its proof and the remark following it on infinite fans, which states the theorem) and Section 1.
- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Section 1, which states that the undecidability needs two binary and infinitely many monadic predicate letters.
