# Cycles in chemical organizations

A reaction network is a pair $(\mathcal M, \mathcal R)$ of a finite set of species and a finite set of reactions $l \to r$, where $l, r$ are multisets over $\mathcal M$. Write $\mathrm{supp}(l \to r)$ and $\mathrm{prod}(l \to r)$ for the sets of species occurring in $l$ and in $r$, and $\mathcal R_A$ for the reactions with $\mathrm{supp} \subseteq A$, for $A \subseteq \mathcal M$. Let $\mathbf S$ be the stoichiometric matrix of $\mathcal R_A$ restricted to $A$.

- $A$ is *closed* if $\mathrm{prod}(\rho) \subseteq A$ for every $\rho \in \mathcal R_A$.
- $A$ is *semi-self-maintaining* if every species consumed by some reaction in $\mathcal R_A$ is produced by some reaction in $\mathcal R_A$.
- $A$ is *self-maintaining* if there is a flux vector $v$ with $v_\rho > 0$ for all $\rho \in \mathcal R_A$ and $\mathbf S v \ge 0$. A closed self-maintaining set is an *organization*; every organization is semi-self-maintaining.
- $A$ is *reactive* if every species of $A$ occurs in the support of some reaction of $\mathcal R_A$.
- Species $a$ is *directly causally connected* to $b$, written $a \to b$, if some reaction has $a$ in its support and $b$ in its product. A *cycle* is a set $\{a_1, \dots, a_n\}$ with $a_1 \to a_2 \to \cdots \to a_n \to a_1$ ($n = 1$ allowed).

1. **Cycles are necessary.** If $B$ is a reactive semi-self-maintaining set that strictly contains a closed set $A$, then $B \setminus A$ contains a cycle.
2. **Organizations differ by cycles.** If $O_1 \subsetneq O_2$ are reactive organizations, then $O_2$ contains at least one cycle not contained in $O_1$. Hence every reactive organization other than the smallest one (the closure of the inflow) contains a cycle, and organizations are ordered like their sets of cycles.

For mass-action (and other standard) kinetics the set of species with positive concentration at any fixed point is an organization. Therefore any transition between steady states with different sets of reacting species requires adding or removing a cycle.

## Expansion

For item 1, one first shows from reactivity of $B$ and closedness of $A$ that some reaction in $\mathcal R_B$ consumes a species of $B \setminus A$. Let $x_1 \in B \setminus A$ be consumed. By semi-self-maintenance some reaction produces $x_1$, and since $A$ is closed its support must contain a species $x_2 \in B \setminus A$, so $x_2 \to x_1$. Repeating the argument from $x_2$ gives an infinite backward chain in the finite set $B \setminus A$, which must revisit a species and so closes a cycle. Item 2 follows by taking $A = O_1$ and $B = O_2$, since organizations are closed and semi-self-maintaining. The closed-subset hypothesis is needed: a network whose species are all made from the inflow can be self-maintaining without any cycle. In a reflexive autocatalytic network, where each species catalyses the production of the next around a cycle, the positive feedback of that cycle gives a stable positive fixed point. Examples include the mitotic spindle assembly and spindle position checkpoints.

## Sources

- P. Kreyssig, G. Escuela, B. Reynaert, T. Veloz, B. Ibrahim, P. Dittrich, "Cycles and the qualitative evolution of chemical systems", *PLoS ONE* (2012), Methods (closure, self-maintenance, organizations, reactive sets) and Results (Definition 1, Lemma 1 with proof, Corollary 1, "A Particular Autocatalytic Network"), <https://doi.org/10.1371/journal.pone.0045772> (PMC3469651).
