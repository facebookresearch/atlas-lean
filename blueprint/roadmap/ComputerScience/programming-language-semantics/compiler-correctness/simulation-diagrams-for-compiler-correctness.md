# Simulation diagrams for compiler correctness

Let programs $P_1$ and $P_2$ of two languages have small-step semantics with global environments $G_1$, $G_2$, initial and final states, and transitions $G \vdash S \xrightarrow{t} S'$ labelled by traces of events. A program *converges* with trace $t$ and result $n$ if it reaches a final state with result $n$ from an initial state by transitions with trace $t$, *diverges* with trace $T$, finite or infinite, if it performs an infinite sequence of transitions with trace $T$ from an initial state, in the coinductive sense of [transition semantics and simulation relations](transition-semantics-and-simulation-relations.md), and *goes wrong* with trace $t$ if it reaches by $t$ a state that is not final and has no transition; the going-wrong behaviors form $\mathrm{Wrong}$. Let $\sim$ be a relation between states of $P_1$ and of $P_2$ such that

- *initial states*: every initial state of $P_1$ is related by $\sim$ to some initial state of $P_2$;
- *final states*: if $S_1 \sim S_2$ and $S_1$ is final with result $n$, then so is $S_2$.

If $\sim$ is a *lock-step simulation*, meaning that $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t} S_2'$ and $S_1' \sim S_2'$, or, for a measure $|\cdot|$ on the states of $P_1$ with values in a well-founded order, a *star simulation*, meaning that $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give either $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{+} S_2'$ and $S_1' \sim S_2'$, or $|S_1'| < |S_1|$ and $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{*} S_2'$ and $S_1' \sim S_2'$, then $P_1 \Downarrow B$ and $B \notin \mathrm{Wrong}$ imply $P_2 \Downarrow B$: forward simulation for safe programs. Without the decreasing measure, allowing $P_2$ to take zero steps would not preserve divergence, since $P_1$ could stutter infinitely while $P_2$ is stuck. If moreover $P_2$ is deterministic, every behavior of $P_2$ is a behavior of $P_1$ whenever $P_1$ is safe and has at least one behavior. The last hypothesis is needed: if $P_1$ has no initial state, the empty relation satisfies all the conditions above, while $P_2$ may have an initial state that is final with result $0$ and so a behavior that $P_1$ lacks. With it, forward simulation transfers a behavior of $P_1$ to $P_2$, and determinism makes it the only behavior of $P_2$.

## Depends on

- [Notions of semantic preservation](notions-of-semantic-preservation.md)
- [Transition semantics and simulation relations](transition-semantics-and-simulation-relations.md)

## Proof depends on

- [Plus and option simulations are star simulations](plus-and-option-simulations-are-star-simulatio.md)
- [Star simulations preserve finite runs](star-simulations-preserve-finite-runs.md)
- [Measured divergence implies divergence](measured-divergence-implies-divergence.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Sections 2.1, 3.5 and 3.7, Definitions 10 and 12, Theorems 3 and 4 and Figure 4. The condition on initial states, that every initial state of $P_1$ is related to some initial state of $P_2$, follows the CompCert Coq development; Section 3.7 states it as "if initial$(P_1, S_1)$ and initial$(P_2, S_2)$, then $S_1 \sim S_2$", which holds vacuously when $P_2$ has no initial state.
