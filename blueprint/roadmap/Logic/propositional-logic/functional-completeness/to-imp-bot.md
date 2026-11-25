# Translation into $\to$ and $\bot$

The translation $A^*$ of a proposition $A$ is defined
by recursion on $A$: each atom is unchanged, $(A \to B)^* = A^* \to B^*$,
$(A \wedge B)^* = (A^* \to (B^* \to \bot)) \to \bot$ and $(A \vee B)^* = (A^* \to \bot) \to B^*$.
