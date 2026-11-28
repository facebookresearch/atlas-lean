# Finiteness of reachability sets of lossy counter machines is Σ⁰₁-complete

Whether a lossy counter machine reaches only finitely many configurations from a given one is $\Sigma^0_1$-complete, and the complementary question whether it has an unbounded run is $\Pi^0_1$-complete. Undecidability of finiteness is due to Mayr.

**Problems (Schnoebelen).** For a lossy counter machine $M$ and a configuration $\sigma_0$:

- *Finiteness:* is the reachability set $\mathrm{Post}^\ast(\sigma_0)$ finite, equivalently, is there a bound $N$ with $|\sigma| \le N$ for every reachable $\sigma$, where $|\sigma|$ is the sum of the counter values?
- *Unbounded run:* is there an infinite run from $\sigma_0$ that visits infinitely many different configurations?

The two problems are complementary: if $\mathrm{Post}^\ast(\sigma_0)$ is infinite, König's lemma applied to the runs that visit no configuration twice yields an infinite such run.

**Theorem (Schnoebelen).** Finiteness is $\Sigma^0_1$-complete and unbounded run is $\Pi^0_1$-complete for lossy counter machines.

The same source shows that uniform finiteness (finiteness from every configuration) is $\Pi^0_2$-complete.

## Depends on

- [Lossy counter machines](lossy-counter-machines.md)
- [Σ_n sets](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Π_n sets](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [König's lemma for finitely branching graphs](../../../petri-nets/decision-procedures/konig-s-lemma-for-finitely-branching-graphs.md)

## Expansion

For hardness, a Minsky machine $M$ is put on a budget: an extra counter $B$ balances every increment and decrement, and an increment that would exceed the budget leads instead to a terminal location $\ell_{\mathrm{bankrupt}}$. The new machine starts at $\ell_1$, increments $B$ once when entering $\ell_{\mathrm{init}}$, runs the budgeted machine, and from $\ell_{\mathrm{bankrupt}}$ moves the total of all counters back into $B$, resets the others and returns to $\ell_1$. Along an unbounded lossy run the budget values at successive visits of $\ell_1$ grow by at most $1$ at a time and take every value; whenever the budget reaches a new maximum, the preceding round was loss-free and so simulated a run of $M$ of that size. Hence $M$ has an unbounded run from $\langle \ell_{\mathrm{init}}, \vec{0} \rangle$ if and only if the new machine has an unbounded lossy run. Existence of an unbounded run of a Minsky machine is $\Pi^0_1$-complete, so finiteness is $\Sigma^0_1$-hard.

## Sources

- Philippe Schnoebelen, "Lossy Counter Machines Decidability Cheat Sheet", Reachability Problems (RP 2010), Lecture Notes in Computer Science, pp. 51–75, 2010, <https://doi.org/10.1007/978-3-642-15349-5_4>; Section 6 (problem definitions, Theorems 6.1 and 6.2) and Sections 7.1 and 7.4 (budgets, Proposition 7.5 and Corollary 7.6), read in the open-access copy at <http://www.lsv.fr/Publis/PAPERS/PDF/phs-rp10.pdf>.
- Richard Mayr, "Undecidable problems in unreliable computations", *Theoretical Computer Science* 297(1–3), pp. 337–354, 2003, doi:[10.1016/S0304-3975(02)00646-1](https://doi.org/10.1016/S0304-3975(02)00646-1), credited by Schnoebelen (introduction) with the undecidability of finiteness; not read, cited beside the copy read above.
