# LTL and CTL model checking of lossy channel systems is undecidable

Model checking linear-time or branching-time propositional temporal logic over lossy channel systems is undecidable, because already the property "a given control state is visited only finitely often" cannot be checked.

**Model checking.** Let $L$ be a [lossy channel system](lossy-channel-systems.md) with control states $S$ and let $f : S \to 2^{\mathit{Prop}}$ label control states with atomic propositions. Formulas of propositional linear-time temporal logic (PTL, also called LTL) are built from propositions with Boolean connectives, next and until, and are evaluated on the computations of $L$: a proposition $p$ holds at position $i$ of a computation iff $p \in f(s)$ for the control state $s$ of its $i$-th global state, and $\Diamond \varphi = \mathit{true}\ \mathcal{U}\ \varphi$, $\Box \varphi = \neg \Diamond \neg \varphi$. $L$ satisfies $\varphi$ under $f$ if every computation of $L$ satisfies $\varphi$ at position $0$. The PTL model checking problem asks, given $L$, $f$ and $\varphi$, whether $L$ satisfies $\varphi$ under $f$; the CTL model checking problem is defined in the same way for computation tree logic.

**Theorem (Abdulla and Jonsson).**

1. The model checking problem for PTL interpreted over lossy channel systems is undecidable (Theorem 5.1).
2. The model checking problem for CTL interpreted over lossy channel systems is undecidable (Theorem 5.2).

Both already fail for one fixed formula: $\Diamond \Box \neg p$ for PTL and $\mathrm{AF}\,\mathrm{AG}\,\neg p$ for CTL, with $p$ true exactly at one control state.

## Depends on

- [Lossy channel systems](lossy-channel-systems.md)
- [Formulas of linear temporal logic](../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [CTL formulas](../../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Recurrent control-state reachability for lossy channel systems is undecidable](recurrent-control-states-of-lossy-channel.md)

## Expansion

Given $L$ and a control state $s$, let $p$ hold exactly at $s$. Then $L$ fails $\Diamond \Box \neg p$ iff some computation visits $s$ infinitely often, so the recurrent state problem reduces to PTL model checking; the CTL case uses $\mathrm{AF}\,\mathrm{AG}\,\neg p$ in the same way. The source also shows that eventuality properties become undecidable under fairness conditions on the channels (Section 6).

## Sources

- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", in *Automata, Languages and Programming (ICALP 1994)*, Lecture Notes in Computer Science 820, Springer, 1994, pp. 316–327, doi:10.1007/3-540-58201-0_78; read in the authors' archived copy at <https://www.it.uu.se/research/docs/fm/apv/publications/files/icalp94.ps>: Section 5 (the definition of PTL over lossy channel systems and Theorems 5.1 and 5.2) of that copy.
- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", *Information and Computation* 130(1):71–90, 1996, doi:10.1006/inco.1996.0083 (the journal version; not read).
