# Plus and option simulations are star simulations

With the setting of [transition semantics and simulation relations](transition-semantics-and-simulation-relations.md), let $\sim$ relate states of $P_1$ and $P_2$, and let $|\cdot|$ be a measure on the states of $P_1$ with values in a well-founded order.

- $\sim$ is a *plus simulation* if $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{+} S_2'$ and $S_1' \sim S_2'$.
- $\sim$ is an *option simulation* if $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give either $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t} S_2'$ and $S_1' \sim S_2'$, or $|S_1'| < |S_1|$, $t = \varepsilon$ and $S_1' \sim S_2$.

Every lock-step simulation is a plus simulation, and every plus simulation and every option simulation is a star simulation. Hence each of them, together with the conditions on initial and final states, gives forward simulation for safe programs, as in [simulation diagrams](simulation-diagrams-for-compiler-correctness.md).

**Proof.** One transition is a nonempty sequence of transitions, and a stuttering step of an option simulation is a step of length zero with a decreasing measure.

## Depends on

- [Transition semantics and simulation relations](transition-semantics-and-simulation-relations.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 3.7, Definitions 10, 12, 13 (plus simulation) and 14 (option simulation), the remark after them, and Figure 4.
