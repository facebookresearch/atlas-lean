# Notions of semantic preservation

Let the semantics of a source language and of a target language associate with each program a set of *observable behaviors*, including termination, divergence and "going wrong" on an undefined computation, together with the traces of input-output operations performed; write $S \Downarrow B$ when program $S$ can execute with behavior $B$, and let $\mathrm{Wrong}$ be the set of going-wrong behaviors. A program $S$ is *safe* if none of its behaviors is in $\mathrm{Wrong}$, and *deterministic* if $S \Downarrow B_1$ and $S \Downarrow B_2$ imply $B_1 = B_2$. For a source program $S$ and its compiled program $C$:

- *bisimulation*: $S \Downarrow B \iff C \Downarrow B$ for all $B$;
- *backward simulation*: $C \Downarrow B \implies S \Downarrow B$ for all $B$; *for safe programs*, the same under the hypothesis that $S$ is safe;
- *forward simulation*: $S \Downarrow B \implies C \Downarrow B$ for all $B$; *for safe programs*, the same for all $B \notin \mathrm{Wrong}$;
- *preservation of a specification* $\mathrm{Spec}$, a predicate on behaviors that excludes $\mathrm{Wrong}$: if every behavior of $S$ satisfies $\mathrm{Spec}$, so does every behavior of $C$;
- *preservation of safety*: if $S$ is safe, so is $C$.

If $C$ is deterministic, forward simulation implies backward simulation, and forward simulation for safe programs implies backward simulation for safe programs; the converse implications hold if $S$ is deterministic. Backward simulation for safe programs implies preservation of every specification.

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 2.1, Definitions 1–7 and Figure 2
