# Probabilistic higher-order fixpoint logic

PHFL is a probabilistic, higher-order extension of the modal μ-calculus: its formulas denote quantitative predicates on the states of a finite Markov chain, and fixpoints and λ-abstractions may range over higher-order functions on them.

**Definition.** A *Markov chain* over $AP$ is $M = (S, P, \rho, s_{\mathrm{in}})$ with a finite set $S$ of states, transition probabilities $P : S \times S \to [0, 1]$ with $\sum_{s'} P(s, s') = 1$ for each $s$, a labeling $\rho : AP \to 2^S$ ($AP$ closed under negation of propositions) and an initial state. *Types* are $\tau ::= \mathrm{Prop} \mid \tau_1 \to \tau_2$, with $\mathrm{order}(\mathrm{Prop}) = 0$ and $\mathrm{order}(\tau_1 \to \tau_2) = \max(\mathrm{order}(\tau_1) + 1, \mathrm{order}(\tau_2))$. Formulas are

$$
\varphi ::= p \mid X \mid \varphi \vee \varphi \mid \varphi \wedge \varphi \mid [\varphi]_J \mid \square\varphi \mid \lozenge\varphi \mid \bigcirc\varphi \mid \mu X.\varphi \mid \nu X.\varphi \mid \lambda X.\varphi \mid \varphi\,\varphi,
$$

with $J$ of the form $> r$ or $\ge r$ for rational $r \in [0, 1]$, restricted to well-typed formulas. A formula of type $\mathrm{Prop}$ denotes a function $S \to [0, 1]$: $p$ is the indicator of $\rho(p)$, $\vee$ and $\wedge$ are pointwise maximum and minimum, $[\varphi]_J$ is $1$ where the value of $\varphi$ lies in $J$ and $0$ elsewhere, $\square\varphi$, $\lozenge\varphi$ and $\bigcirc\varphi$ are the minimum, maximum and $P$-weighted average of the value of $\varphi$ over the successors ($P(s, s') > 0$), and $\mu$, $\nu$ are least and greatest fixpoints of monotone functions on the domains of their types, $\lambda$ and application being function abstraction and application. The *order* of a formula is the largest order of a type in its typing derivation; order-0 PHFL is the $\mu^p$-calculus. For a closed formula $\varphi$ of type $\mathrm{Prop}$, $M \models \varphi$ iff the value of $\varphi$ at $s_{\mathrm{in}}$ is $1$, and the *model-checking problem* asks, given $M$ and $\varphi$, whether $M \models \varphi$; as an input, $M$ is given by finite tables with rational transition probabilities.

## Depends on

- [Discrete-time Markov chains](../discrete-time-markov-chains.md)
- [Formulas of the modal μ-calculus](../../../modal-logic/modal-calculus/mu-formula.md)

## Proof depends on

None.

## Expansion

Only the thresholds $> r$ and $\ge r$ are allowed, which keeps every formula monotone, so the fixpoints exist. Order-1 PHFL is strictly more expressive than the $\mu^p$-calculus (Theorem 2.9 of the source), and model checking is decidable for the $\mu^p$-calculus and for non-probabilistic higher-order fixpoint logic.

## Sources

- Y. Mitani, N. Kobayashi and T. Tsukada, "A Probabilistic Higher-order Fixpoint Logic", *Logical Methods in Computer Science* 17(4), 2021, paper 15, pp. 15:1–15:36, <https://doi.org/10.46298/lmcs-17(4:15)2021>; numbers from arXiv:2011.14303v4, <https://arxiv.org/abs/2011.14303v4>: Definition 2.1, Section 2.2 (syntax, types, order), Section 2.3 (semantics, the relation $M \models \varphi$), Theorem 2.9 and Definition 3.1.
