# Strategy logic

Strategy logic SL extends LTL with first-order quantification over strategies, $\langle\langle x\rangle\rangle\varphi$ and $[[x]]\varphi$, and bindings $(a, x)\varphi$ that make agent $a$ follow the strategy held by variable $x$; it is interpreted on concurrent game structures.

**Models.** A *concurrent game structure* is $\mathcal{G} = \langle \mathrm{AP}, \mathrm{Ag}, \mathrm{Ac}, \mathrm{St}, s_0, \lambda, \tau\rangle$ with finite nonempty sets $\mathrm{AP}$ of atomic propositions and $\mathrm{Ag}$ of agents, countable nonempty sets $\mathrm{Ac}$ of actions and $\mathrm{St}$ of states, an initial state $s_0$, a labeling $\lambda : \mathrm{St} \to 2^{\mathrm{AP}}$ and a transition function $\tau : \mathrm{St} \times \mathrm{Ac}^{\mathrm{Ag}} \to \mathrm{St}$ taking a state and a decision (an action for each agent) to a state. A *track* is a finite nonempty sequence of states following transitions, and a *strategy* is a function from tracks to actions.

**Syntax.** With $p \in \mathrm{AP}$, $x$ a variable and $a \in \mathrm{Ag}$:

$$
\varphi ::= p \mid \neg\varphi \mid \varphi \wedge \varphi \mid \varphi \vee \varphi \mid X\varphi \mid \varphi\, U \varphi \mid \varphi\, R\, \varphi \mid \langle\langle x\rangle\rangle\varphi \mid [[x]]\varphi \mid (a, x)\varphi.
$$

Free variables are those not under a quantifier; an agent is free in $\varphi$ when it occurs unbound in the scope of a temporal operator (temporal operators make all agents free, and $(a, x)$ removes $a$ and introduces $x$). A *sentence* has neither free variables nor free agents.

**Semantics.** Under an assignment $\chi$ of strategies to variables and agents, $\langle\langle x\rangle\rangle\varphi$ is true at $s$ if some strategy $f$ makes $\varphi$ are true under $\chi[x \mapsto f]$, $[[x]]\varphi$ if every strategy does, and $(a, x)\varphi$ is true if $\varphi$ is true under $\chi[a \mapsto \chi(x)]$. When every agent is bound, the strategies determine a unique play from $s$, and $X$, $U$, $R$ are evaluated on it as in LTL, with the assignment shifted along the play. A sentence $\varphi$ is *satisfiable* if $\mathcal{G}, \varnothing, s_0 \models \varphi$ for some concurrent game structure $\mathcal{G}$, and *satisfiable on finite models* if such a $\mathcal{G}$ with finitely many states and actions exists.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

LTL is the fragment without quantifiers and bindings, and ATL* embeds into SL: $\langle\langle A\rangle\rangle\psi$ says that the agents in $A$ have strategies such that, for all strategies of the other agents, $\psi$ holds on the resulting play. Model checking SL is nonelementary-hard; its one-goal fragment SL[1G] has 2EXPTIME-complete satisfiability.

## Sources

- F. Mogavero, A. Murano, G. Perelli and M. Y. Vardi, "Reasoning about strategies: on the satisfiability problem", *Logical Methods in Computer Science* 13(1), Paper 9, 2017, doi:10.23638/LMCS-13(1:9)2017; read as arXiv:1611.08541v3, <https://arxiv.org/abs/1611.08541v3>: Section 2 (concurrent game structures, syntax, free agents and variables, strategies, assignments, plays and semantics of SL).
