# Leaves of bounded symbolic execution: terminal or cut off

A symbolic path is a record of a guard (a Boolean expression), a symbolic store $\sigma : \mathbb{N} \to \mathrm{AExp}$ (expressions over the initial state) and a cost $n \in \mathbb{N}$. A leaf of bounded symbolic execution is either a terminal leaf $\operatorname{done}(p)$, for a path $p$ that reached the end of the command, or a cutoff leaf $\operatorname{cut}(p)$, for a path $p$ whose exploration stopped at the budget.
