# Confluence of a relation

Let $(A, \to)$ be an [abstract reduction system](abstract-reduction-system.md). Elements $b, c \in A$ are *joinable*, written $b \downarrow c$, if $b \to^* a \leftarrow^* c$ for some $a \in A$. The relation $\to$ is called

- *Church–Rosser* if $b \leftrightarrow^* c$ implies $b \downarrow c$;
- *confluent* if $b \leftarrow^* a \to^* c$ implies $b \downarrow c$;
- *locally confluent* if $b \leftarrow a \to c$ implies $b \downarrow c$;
- *convergent* if it is confluent and terminating.

## Depends on

- [Abstract reduction system](abstract-reduction-system.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.3, p. 110: joinability, Church–Rosser property, confluence, local confluence and convergence.
