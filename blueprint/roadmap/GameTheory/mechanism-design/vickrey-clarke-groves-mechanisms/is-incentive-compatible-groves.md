# Vickrey–Clarke–Groves theorem

Throughout, $I$ is a finite set of agents and $A$ a set of alternatives; a valuation profile $v = (v_i)_{i \in I}$ gives each agent a valuation $v_i : A \to \mathbb{R}$, and $(w, v_{-i})$ denotes the profile $v$ with $v_i$ replaced by $w$.
If the alternative rule $f$ chooses a welfare-maximizing alternative for every reported profile
($W(v, a) \le W(v, f(v))$ for all $v$ and $a$) and the pivot terms do not depend on the agents' own
reports, then the mechanism that uses $f$ and charges the Groves payments is incentive compatible
(Nisan 2007, Theorem 9.17).

## Informally uses

- [VCG truthfulness, pointwise](groves-payment-truthful.md): applied to every agent, profile and report.

## Background

- [Gibbard–Satterthwaite theorem](../../social-choice/gibbard-satterthwaite-theorem/README.md): without money nothing nontrivial is strategy-proof; quasi-linear utilities and transfers are what VCG mechanisms use to escape it.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.16 and Theorem 9.17.
