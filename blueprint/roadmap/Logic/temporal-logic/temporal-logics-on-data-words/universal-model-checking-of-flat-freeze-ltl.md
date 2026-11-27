# Universal model checking of one-counter automata against flat freeze LTL is undecidable

Checking whether some run of a one-counter automaton satisfies a flat freeze LTL sentence is NEXPTIME-complete, but checking whether all runs satisfy it is undecidable.

**One-counter automata.** A one-counter automaton (OCA) has a finite set of states with an initial state, a labeling of states by finite sets of atomic propositions, and transitions that add an integer to a counter ranging over $\mathbb N$ or test it against a constant; a run is an infinite sequence of configurations in which the counter never becomes negative. A run induces the data word $(P_0,v_0)(P_1,v_1)\cdots$ of state labels $P_i$ and counter values $v_i$.

**Freeze LTL.** Formulas of freeze LTL are

$$
\phi::=p\mid{\bowtie}\,r\mid\neg\phi\mid\phi\vee\phi\mid\phi\wedge\phi\mid\mathsf X\phi\mid\phi\,\mathsf U\,\phi\mid\phi\,\mathsf R\,\phi\mid{\downarrow_r}\phi,
$$

with $p$ an atomic proposition, $r$ a register and ${\bowtie}\in\{<,=,>\}$. The *freeze quantifier* ${\downarrow_r}\phi$ stores the current counter value in register $r$, and the register test ${\bowtie}\,r$ compares the current counter value with the content of $r$. A formula is *flat* if for every occurrence of $\phi_1\,\mathsf U\,\phi_2$ (respectively $\phi_2\,\mathsf R\,\phi_1$) under an even number of negations no freeze quantifier occurs in $\phi_1$, and under an odd number of negations none occurs in $\phi_2$; a formula is *co-flat* if its negation is flat. For an OCA $\mathcal M$ and a sentence $\phi$, *universal model checking* asks whether every infinite initialized run of $\mathcal M$ satisfies $\phi$, and *existential model checking* whether some run does.

**Theorem (Bollig, Quaas and Sangnier).** Model checking OCA against co-flat freeze LTL sentences (some run satisfies the sentence) is undecidable. Consequently, universal model checking of OCA against flat freeze LTL sentences is undecidable.

By contrast, existential model checking of OCA, and of OCA with succinct updates, against flat freeze LTL is NEXPTIME-complete, so for the flat fragment the two directions of model checking differ sharply.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Demri, Lazić and Sangnier showed that model checking OCA against full freeze LTL is undecidable; a close inspection of their proof shows that every formula it builds is co-flat, which gives the first statement. Negating the input formula turns "some run satisfies the co-flat sentence $\phi$" into the negation of "every run satisfies the flat sentence $\neg\phi$", which gives the second. A good expansion links a page for the undecidability of model checking one-counter automata against freeze LTL (Demri, Lazić and Sangnier) together with the observation that its formulas are co-flat; no such page exists yet.

## Sources

- B. Bollig, K. Quaas and A. Sangnier, "The complexity of flat freeze LTL", *Logical Methods in Computer Science* 15(3), paper 33, 2019, doi:[10.23638/LMCS-15(3:33)2019](https://doi.org/10.23638/LMCS-15(3:33)2019); read in arXiv:1609.06124v8 ([arXiv](https://arxiv.org/abs/1609.06124v8)): the definitions of one-counter automata, freeze LTL and its flat fragment, the main NEXPTIME-completeness result, and the two undecidability theorems with their proofs in the section on universal model checking.
