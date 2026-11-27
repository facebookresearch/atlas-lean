# Transition semantics and simulation relations

Let programs $P_1$ and $P_2$ of two languages have small-step semantics with global environments $G_1$, $G_2$, predicates for initial states and for final states with an integer result, and transitions $G \vdash S \xrightarrow{t} S'$ labeled by finite traces $t$ of events, $\varepsilon$ being the empty trace. Write $\xrightarrow{t}{}^{*}$ and $\xrightarrow{t}{}^{+}$ for sequences of zero or more and of one or more transitions whose traces concatenate to $t$. A program *converges* with trace $t$ and result $n$ if it reaches a final state with result $n$ from an initial state by a sequence of transitions with trace $t$; it *diverges* with a finite or infinite trace $T$ if $G \vdash S \xrightarrow{T}{}^{\infty}$ holds for an initial state $S$, where $G \vdash S \xrightarrow{T}{}^{\infty}$, *$S$ performs an infinite sequence of transitions with trace $T$*, is defined coinductively: it holds if $G \vdash S \xrightarrow{t} S'$ and $G \vdash S' \xrightarrow{T'}{}^{\infty}$ with $T = t \cdot T'$. With silent steps $T$ is not determined by the run: a state with only a silent self-loop performs an infinite sequence of transitions with every trace $T$, since $T = \varepsilon \cdot T$; the concatenation of the emitted labels is the least such trace for the prefix order. and it *goes wrong* with trace $t$ if it reaches by $t$ a state that is not final and has no transition. These are its observable behaviors, in the sense of [semantic preservation](notions-of-semantic-preservation.md).

Let $\sim$ relate states of $P_1$ and $P_2$ and let $|\cdot|$ be a measure on the states of $P_1$ with values in a well-founded order. The relation satisfies the conditions on *initial states* if every initial state of $P_1$ is related to some initial state of $P_2$, and on *final states* if $S_1 \sim S_2$ and $S_1$ final with result $n$ imply $S_2$ final with result $n$. It is a

- *lock-step simulation* if $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t} S_2'$ and $S_1' \sim S_2'$;
- *star simulation* if $S_1 \sim S_2$ and $G_1 \vdash S_1 \xrightarrow{t} S_1'$ give either $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{+} S_2'$ and $S_1' \sim S_2'$, or $|S_1'| < |S_1|$ and $S_2'$ with $G_2 \vdash S_2 \xrightarrow{t}{}^{*} S_2'$ and $S_1' \sim S_2'$.

## Depends on

- [Notions of semantic preservation](notions-of-semantic-preservation.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 3.5 (transition semantics, traces, the coinductive infinite closure $G \vdash S \xrightarrow{T}{}^{\infty}$ and the behaviors of a program), Section 13.3 (a silently diverging program has behaviors $\mathrm{diverges}(T)$ for every trace $T$, and the minimal trace) and Section 3.7 (the conditions on initial and final states, and Definitions 10 and 12, lock-step and star simulations).
