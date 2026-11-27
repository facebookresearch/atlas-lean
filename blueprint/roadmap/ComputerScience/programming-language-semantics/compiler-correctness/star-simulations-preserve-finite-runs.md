# Star simulations preserve finite runs

With the setting of [transition semantics and simulation relations](transition-semantics-and-simulation-relations.md), let $\sim$ be a star simulation. If $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t}{}^{*} S_1'$, then there is $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{*} S_2'$ and $S_1' \sim S_2'$. The lemma itself starts from a related pair and needs no condition on initial states. Hence, given the conditions on initial and final states, terminating behaviors of $P_1$ are behaviors of $P_2$: a terminating run of $P_1$ from an initial state starts from a state related to some initial state of $P_2$.

**Proof.** Induction on the length of the sequence of transitions of $P_1$; each step is matched by zero or more steps of $P_2$ with the same trace.

## Depends on

- [Transition semantics and simulation relations](transition-semantics-and-simulation-relations.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 3.7, the first step of the proofs of Theorems 3 and 4.
