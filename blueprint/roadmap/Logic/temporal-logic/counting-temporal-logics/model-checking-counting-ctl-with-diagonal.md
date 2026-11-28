# Model checking counting CTL with diagonal and Boolean constraints is undecidable

Model checking finite Kripke structures against counting CTL becomes undecidable as soon as constraints may compare two counts, with coefficients ±1, inside Boolean combinations.

**Theorem (Laroussinie, Meyer and Petonnet).** The [model-checking problem](counting-ctl.md) for CCTL$_{\wedge\pm 1}$ is undecidable: there is no algorithm that decides, given a finite Kripke structure $S$, a state $q$ and a CCTL$_{\wedge\pm 1}$ formula $\Phi$, whose constraints are Boolean combinations of linear constraints with coefficients in $\{-1, 1\}$, whether $q \models \Phi$ (Theorem 4.12 of the source, by a reduction from the halting problem for two-counter machines).

In contrast, model checking CCTL$_{\pm 1}$, with diagonal constraints but no Boolean combinations inside a constraint, is P-complete (Theorem 4.4), and model checking CCTL$_\wedge$ is $\Delta^P_2$-complete (Corollary 4.11). The same undecidability holds for the variant CCTL$^c_{\pm 1}$ with cumulative semantics (Theorem 6.23 of the source).

## Depends on

- [Counting CTL](counting-ctl.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of a two-counter machine $M$ with counters $C$, $D$ and instructions $I_1, \ldots, I_n$: increments $\langle X{+}{+}, j\rangle$, tests $\langle \text{if } X = 0 \text{ then } j \text{ else } X{-}{-}, k\rangle$, and halt. The Kripke structure $S_M$ has a state $q_i$ per instruction; an increment of $X$ is labeled $X^{+}$ and goes to $q_j$; a test has a branch through a state $r_i$ labeled $X^{-}$ to $q_k$ and a branch through states $s_i$, $t_i$ labeled $X^{\bar 0}$ and $X^{0}$ to $q_j$, and the halt state is labeled $\mathit{halt}$. Along a run prefix the value of $X$ is $\sharp X^{+} - \sharp X^{-}$, and the prefix ends in some $s_i$ (a zero test taken) iff $\sharp X^{\bar 0} > \sharp X^{0}$. Then $M$ does not halt iff $q_1 \models \mathsf{EG}_{[C]}\bot$ with

$$
C = (\sharp\mathit{halt} \ge 1) \vee \bigvee_{X \in \{C, D\}} \Big( (\sharp X^{+} - \sharp X^{-} < 0) \vee (\sharp X^{+} - \sharp X^{-} > 0 \wedge \sharp X^{\bar 0} - \sharp X^{0} > 0) \Big),
$$

which says that some run never reaches a prefix that halts or simulates $M$ wrongly (more decrements than increments, or a zero test taken while the counter is positive).

## Sources

- F. Laroussinie, A. Meyer and E. Petonnet, "Counting CTL", *Logical Methods in Computer Science* 9(1), 2013, paper 3, <https://doi.org/10.2168/LMCS-9(1:3)2013>; numbers from arXiv:1211.4651v4, <https://arxiv.org/abs/1211.4651v4>: Section 4.3: Theorem 4.12 and its proof; Theorem 4.4, Corollary 4.11 and Theorem 6.23.
