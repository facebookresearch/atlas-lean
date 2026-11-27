# Machine with security domains

A system in the sense of Goguen–Meseguer noninterference:
a deterministic automaton with states $S$, an initial state $s_0$ (`start`) and a transition
function $\mathrm{step} : S \times A \to S$ (`tr`) on actions $A$, together with an output function
$\mathrm{output} : S \times A \to O$ and a security domain $\mathrm{dom}(a) \in D$ of each action
$a$. The state reached from $s$ by an action sequence $\alpha$ is $\mathrm{run}(s, \alpha)$
(`mtr`), with $\mathrm{run}(s, \Lambda) = s$ and
$\mathrm{run}(s, a \circ \alpha) = \mathrm{run}(\mathrm{step}(s, a), \alpha)$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, Definition 1.
