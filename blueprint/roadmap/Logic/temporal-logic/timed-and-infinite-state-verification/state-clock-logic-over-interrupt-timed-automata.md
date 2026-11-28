# Model checking State Clock Logic over interrupt timed automata is undecidable

Interrupt timed automata have a decidable reachability problem, yet checking a fixed formula of the timed linear-time logic State Clock Logic over them is undecidable, already for automata with three interrupt levels.

**Interrupt timed automata.** An *interrupt timed automaton* (ITA) is a hybrid automaton whose finite set of control states is organized in interrupt levels $1,\dots,n$, with one clock $x_k$ per level. In a state of level $k$ the clock $x_k$ is active and evolves with rate $1$, the clocks of lower levels are suspended (rate $0$) and those of higher levels are irrelevant. Guards on transitions are linear constraints with rational coefficients over the clocks of the current and lower levels, updates assign to clocks linear expressions with rational coefficients in clocks of lower levels, and each state carries a policy (lazy, urgent or delayed) that rules its sojourn time. Reachability for ITA is decidable (in NEXPTIME).

**State Clock Logic.** Formulas of State Clock Logic (SCL) are

$$
\psi::=p\mid\psi\wedge\psi\mid\neg\psi\mid\psi\,\mathsf U\,\psi\mid\psi\,\mathsf S\,\psi\mid\rhd_{\bowtie a}\psi\mid\lhd_{\bowtie a}\psi,
$$

with $p$ an atomic proposition, ${\bowtie}\in\{>,\ge,=,\le,<\}$ and $a$ rational. $\rhd_{\bowtie a}\psi$ holds when the next time $\psi$ holds lies at a delay satisfying ${\bowtie}\,a$, and $\lhd_{\bowtie a}\psi$ when the last time $\psi$ held lies at a past delay satisfying ${\bowtie}\,a$. An ITA $\mathcal A$ satisfies $\varphi$ if every execution of $\mathcal A$ satisfies $\varphi$ at its initial position.

**Theorem (Bérard, Haddad and Sassolas).** Model checking SCL over ITA is undecidable. Specifically, there exists a fixed SCL formula, using only the modalities $\mathsf U$ and $\lhd_{=a}$, such that checking whether a given ITA with $3$ levels satisfies it is undecidable (Theorem 3 of the source).

Model checking SCL over timed automata is PSPACE-complete, so the obstruction comes from the suspended clocks. The source also shows that reachability is undecidable for the product of an ITA with a timed automaton, and identifies fragments of timed CTL that are decidable over ITA.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction simulates a deterministic two-counter machine $\mathcal M$. One builds a fixed formula $\varphi_{2cm}$ and, from $\mathcal M$, an ITA $\mathcal A_{\mathcal M}$ with three clocks such that $\mathcal A_{\mathcal M}\models\varphi_{2cm}$ if and only if $\mathcal M$ does not halt. The clocks of levels $1$ and $2$ hold the two counter values, a value $n$ being stored as $1/2^n$, and level $3$ is the working level. Copying a clock value down to a lower level is impossible in an ITA, so modules of the automaton guess the new values and SCL subformulas, using $\lhd_{=a}$, enforce that the guess is right: one module swaps the contents of $x_1$ and $x_2$, one halves $x_2$ (increment) and one doubles it (decrement), with a zero test. An execution satisfying the formula therefore follows the unique computation of $\mathcal M$, and every execution satisfies it exactly when that computation never reaches the halting instruction.

## Sources

- B. Bérard, S. Haddad and M. Sassolas, "Interrupt timed automata: verification and expressiveness", *Formal Methods in System Design* 40(1), pp. 41–87, 2012, doi:[10.1007/s10703-011-0140-2](https://doi.org/10.1007/s10703-011-0140-2); read in arXiv:1203.6453v1 ([arXiv](https://arxiv.org/abs/1203.6453v1)): Definitions 1 and 2 (interrupt timed automata) in Section 2, Proposition 2 (decidability of reachability) in Section 3, Definition 8 (SCL) and Theorem 3 with its proof in Section 5.1, Theorems 4 and 5 (decidable fragments of timed CTL) in Section 5, and Theorem 7 (undecidability of reachability for ITA combined with timed automata) in Section 7.
