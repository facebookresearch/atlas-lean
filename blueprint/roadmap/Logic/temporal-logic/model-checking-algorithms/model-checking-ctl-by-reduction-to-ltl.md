# Model checking CTL* by reduction to LTL

Let $M$ be a finite Kripke structure with a total transition relation and $\varphi$ a CTL$^*$ state formula. The set $\mathrm{Sat}(\varphi)$ of states satisfying $\varphi$ is computable as follows. Take the maximal-depth state subformulas of the form $\mathbf{E}\, \pi$ in turn, innermost first; $\mathbf{A}\, \pi$ is read as $\neg \mathbf{E} \neg \pi$. For each one:
1. by the time it is processed, all state subformulas inside $\pi$ have been replaced by fresh atomic propositions, so $\pi$ is an LTL formula;
2. compute the set of states $s$ with some path from $s$ satisfying $\pi$, using an LTL model-checking procedure on $\neg\pi$: $s \models \mathbf{E}\, \pi$ if and only if not every path from $s$ satisfies $\neg\pi$;
3. add a fresh proposition $p_{\mathbf{E}\pi}$ labelling exactly those states, and replace $\mathbf{E}\, \pi$ by it.

At the end, $\varphi$ has become a propositional formula over the original and fresh propositions, and $\mathrm{Sat}(\varphi)$ can be read off the labels.

**Theorem.** The procedure terminates and computes $\mathrm{Sat}(\varphi)$. Its running time is polynomial in $|M|$ and exponential in $|\varphi|$, dominated by the LTL checks.

**Proof.** There are at most $|\varphi|$ state subformulas, and each step is one call of a terminating LTL model-checking procedure on a finite structure. Correctness of each replacement step is the [abstraction lemma](replacing-a-ctl-state-subformula-by-a-fresh-atom.md), applied once per step, and induction over the steps gives the result.

## Depends on

- [State formulas of CTL$^*$](../ctl/ctl-state-and-path-formulas/state-formula.md)

## Proof depends on

- [Replacing a CTL$^*$ state subformula by a fresh atom](replacing-a-ctl-state-subformula-by-a-fresh-atom.md)
- [Correctness of the LTL model-checking procedure](../model-checking-for-linear-temporal-logic/check-b-iff.md)

## Sources

- T. Willemse, *Algorithms for Model Checking (2IW55)*, Lecture 1 "The temporal logics CTL$^*$, CTL and LTL: syntax and semantics", Eindhoven University of Technology, 2008, <https://www.win.tue.nl/%7Etimw/teaching/amc/2008/week1.pdf>: CTL$^*$ syntax and semantics, and the existential and universal path quantifiers. The procedure assembles the abstraction lemma with an effective LTL model-checking procedure.
