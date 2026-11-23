# VCG truthfulness, pointwise

Throughout, $I$ is a finite set of agents and $A$ a set of alternatives; a valuation profile $v = (v_i)_{i \in I}$ gives each agent a valuation $v_i : A \to \mathbb{R}$, and $(w, v_{-i})$ denotes the profile $v$ with $v_i$ replaced by $w$.
Let $f$ be an alternative rule and $(h_i)$ pivot terms that do not depend on the agents' own reports, and
let $p_i$ be the Groves payments. Let $i$ be an agent, $v$ a profile and $w : A \to \mathbb{R}$ a report.
If $f(v)$ has at least the welfare, at the true profile $v$, of the alternative chosen after agent $i$
reports $w$, that is $W(v, f(w, v_{-i})) \le W(v, f(v))$, then agent $i$ does not gain by reporting $w$
instead of $v_i$:

$$v_i\bigl(f(w, v_{-i})\bigr) - p_i(w, v_{-i}) \le v_i(f(v)) - p_i(v).$$

## Informally uses

- [Welfare decomposition](welfare-eq.md) and [the others' welfare ignores the own valuation](others-welfare-update.md): the utility of agent $i$ is the social welfare minus a term it does not influence.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, proof of Theorem 9.17.
