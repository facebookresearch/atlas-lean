# Measured divergence implies divergence

With the setting of [transition semantics and simulation relations](transition-semantics-and-simulation-relations.md), let $<$ be a well-founded order on a set $M$. Define coinductively that $P_2$ *diverges from $S_2$ with measure $\mu \in M$ and trace $T$* if either $G_2 \vdash S_2 \xrightarrow{t}{}^{+} S_2'$ and $P_2$ diverges from $S_2'$ with some measure $\mu'$ and trace $T'$, where $T = t \cdot T'$, or $G_2 \vdash S_2 \xrightarrow{t}{}^{*} S_2'$ and $P_2$ diverges from $S_2'$ with a measure $\mu' < \mu$ and trace $T'$, where $T = t \cdot T'$.

1. If $\sim$ is a star simulation with measure $|\cdot|$, $S_1 \sim S_2$ and $P_1$ performs an infinite sequence of transitions from $S_1$ with trace $T$, then $P_2$ diverges from $S_2$ with measure $|S_1|$ and trace $T$.
2. If $P_2$ diverges from $S_2$ with some measure and trace $T$, then $P_2$ performs an infinite sequence of transitions from $S_2$ with trace $T$.

**Proof idea.** Part 1 by coinduction. Part 2 by coinduction, using the inversion lemma, proved by well-founded induction on $\mu$, that measured divergence from $S_2$ yields one transition $G_2 \vdash S_2 \xrightarrow{t} S_2'$ with measured divergence from $S_2'$ and trace $T'$, where $T = t \cdot T'$: the second rule can be applied only finitely often in a row because the measure decreases.

## Depends on

- [Transition semantics and simulation relations](transition-semantics-and-simulation-relations.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 3.7, the proof of Theorem 4: the coinductive measured divergence relation, the coinduction from a star simulation, and the inversion lemma proved by Noetherian induction over $\mu$.
