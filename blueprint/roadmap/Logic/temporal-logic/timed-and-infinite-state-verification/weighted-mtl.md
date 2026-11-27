# Weighted MTL

Weighted MTL is the extension of LTL whose until operators are constrained by bounds on an accumulated cost; it is evaluated on finite runs of labeled priced timed automata.

Formulas are $\varphi ::= a \mid \neg\varphi \mid \varphi \vee \varphi \mid \varphi\, U_{\mathrm{cost} \sim c}\, \varphi$ with $a$ an atomic proposition, $\mathrm{cost}$ one of the cost functions, $c \in \mathbb{N}$ and $\sim\, \in \{<, \leq, =, \geq, >\}$. On a finite run $\varrho$, $\varrho \models \varphi_1\, U_{\mathrm{cost} \sim c}\, \varphi_2$ iff some position $0 < \pi \leq |\varrho|$ has $\varrho_{\geq\pi} \models \varphi_2$, every $0 < \pi' < \pi$ has $\varrho_{\geq\pi'} \models \varphi_1$, and the cost of the prefix $\varrho_{\leq\pi}$ satisfies $\sim c$.

The (existential) model-checking problem asks, given $\mathcal{A}$ and $\varphi$, whether some finite run from the initial state satisfies $\varphi$; since the logic is closed under negation, the results transfer to the universal problem.

## Depends on

- [Priced timed automata](priced-timed-automata.md)
- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Since clocks can be used as costs, weighted MTL subsumes MTL with time-bounded until. The branching-time counterpart WCTL is decidable (PSPACE-complete) on one-clock priced timed automata but undecidable from three clocks on.

## Sources

- P. Bouyer, K. G. Larsen and N. Markey, "Model checking one-clock priced timed automata", *Logical Methods in Computer Science* 4(2), Paper 9, 2008, doi:10.2168/LMCS-4(2:9)2008; read as arXiv:0805.1457v2, <https://arxiv.org/abs/0805.1457v2>: Section 3.1 and Definition 3.1 of arXiv:0805.1457v2, with Theorem 2.3 and Section 2.1 (WCTL).
