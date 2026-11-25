# Delete relaxation

A STRIPS task in positive normal form has a finite set of atoms, an initial state (a set of atoms), a
goal (a set of atoms) and operators $o$ with precondition $\mathrm{pre}(o)$, add list $\mathrm{add}(o)$
and delete list $\mathrm{del}(o)$, all sets of atoms, with no negative preconditions or goals. Its delete
relaxation is the task with every delete list replaced by the empty set; a relaxed plan is a plan of the
relaxed task. The relaxed reachable set from a state $s$ is the least set $R \supseteq s$ such that
$\mathrm{pre}(o) \subseteq R$ implies $\mathrm{add}(o) \subseteq R$ for every operator $o$, the least fixed
point of $R \mapsto R \cup \bigcup \{\mathrm{add}(o) : \mathrm{pre}(o) \subseteq R\}$ above $s$. Tasks with
negative preconditions or goals must first be compiled to positive normal form.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Propositional STRIPS tasks.

## Sources

- Foundations of AI: Automated Planning: Delete Relaxation Heuristics (slides) — University of Basel AI course (Helmert group), relaxed planning graph slides. <https://ai.dmi.unibas.ch/_files/teaching/fs26/ai/slides/ai-f04-handout4.pdf>
