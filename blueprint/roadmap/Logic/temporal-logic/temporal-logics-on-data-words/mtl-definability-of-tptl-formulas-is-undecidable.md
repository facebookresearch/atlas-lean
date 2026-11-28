# MTL-definability of TPTL formulas over non-monotonic data words is undecidable

Over infinite data words with natural-number data values that need not increase, no algorithm decides whether a formula of timed propositional temporal logic is equivalent to a formula of metric temporal logic; the same holds for definability in freeze LTL, in unary TPTL, and in the formulas of a smaller until-rank.

**Data words.** For a finite set $P$ of propositions, an $\omega$-data word is an infinite sequence $w=(P_0,d_0)(P_1,d_1)\cdots$ in $(2^P\times\mathbb N)^\omega$; the data values $d_i$ may decrease, as along the counter values of a run of a one-counter machine.

**MTL and TPTL.** Formulas of metric temporal logic (MTL) are $\varphi::=p\mid\neg\varphi\mid\varphi_1\wedge\varphi_2\mid\varphi_1\,\mathsf U_I\,\varphi_2$, where $I\subseteq\mathbb Z$ is an interval over the integers; $(w,i)\models\varphi_1\,\mathsf U_I\,\varphi_2$ if some $j>i$ has $(w,j)\models\varphi_2$ and $d_j-d_i\in I$, with $\varphi_1$ holding strictly between. Formulas of timed propositional temporal logic (TPTL) are $\varphi::=p\mid x\in I\mid\neg\varphi\mid\varphi_1\wedge\varphi_2\mid\varphi_1\,\mathsf U\,\varphi_2\mid x.\varphi$ over register variables $x$: $x.\varphi$ stores the current data value in $x$, and $x\in I$ says that the current data value minus the stored one lies in $I$; registers initially hold $d_0$. Every MTL formula translates effectively into an equivalent TPTL formula. *Freeze LTL* is the fragment of TPTL whose register constraints are $x\in[0,0]$, *unary TPTL* allows only the temporal operators $\mathsf X$ and $\mathsf F$, and $\mathrm{MTL}_k$, $\mathrm{TPTL}_k$ consist of the formulas of until-rank at most $k$. A TPTL formula is *definable* in a fragment if some formula of the fragment defines the same set of data words.

**Theorem (Carapelle, Feng, Fernández Gil and Quaas).**

1. It is undecidable whether a given TPTL formula is definable in MTL (Theorem 3).
2. It is undecidable whether a given TPTL formula is definable in freeze LTL, and whether it is definable in unary TPTL (Proposition 8).
3. There is $m\in\mathbb N$ such that for every $k\ge m$ it is undecidable whether a formula of $\mathrm{MTL}_{k+1}$ is definable in $\mathrm{MTL}_k$, and whether a formula of $\mathrm{TPTL}_{k+1}$ is definable in $\mathrm{TPTL}_k$ (Propositions 5 and 12).

Over such data words TPTL is strictly more expressive than MTL, in contrast with monotonic data words over the natural numbers, where the two logics are equally expressive (Alur and Henzinger).

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The recurrent state problem for two-counter machines, whether some computation visits the initial instruction infinitely often, is $\Sigma^1_1$-hard, and for each machine $M$ there is a TPTL formula $\varphi_M$ without propositions that is satisfiable exactly when $M$ is a positive instance (Alur and Henzinger). Set $\psi_M=(x.\mathsf{FFF}(x=0))\wedge\mathsf F\varphi_M$. If $\varphi_M$ is unsatisfiable, $\psi_M$ defines the empty language and is definable in MTL; if it is satisfiable, an Ehrenfeucht–Fraïssé game argument for MTL shows that $\psi_M$ is not MTL-definable. Hence MTL-definability would decide the recurrent state problem. The same argument with Ehrenfeucht–Fraïssé games for TPTL and its fragments gives parts 2 and 3. A good expansion links pages for Ehrenfeucht–Fraïssé games for MTL and TPTL and for the encoding of two-counter machines in TPTL.

## Sources

- C. Carapelle, S. Feng, O. Fernández Gil and K. Quaas, "On the expressiveness of TPTL and MTL over ω-data words", in *Proceedings of the 14th International Workshop on Automata and Formal Languages (AFL 2014)*, Electronic Proceedings in Theoretical Computer Science 151, pp. 174–187, 2014, doi:[10.4204/EPTCS.151.12](https://doi.org/10.4204/EPTCS.151.12); read in arXiv:1311.6250v2 ([arXiv](https://arxiv.org/abs/1311.6250v2)), whose numbering is used: the definitions of data words, MTL, TPTL and their fragments in the preliminaries, Theorem 3 with its proof, and Propositions 5, 8 and 12.
