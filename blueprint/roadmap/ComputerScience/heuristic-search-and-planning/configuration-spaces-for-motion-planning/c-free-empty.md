# Free space with no obstacles

Let $C$ be a set of configurations, $W$ a workspace, $A : C \to \mathcal{P}(W)$ a placement assigning to each configuration the set of workspace points occupied by the body, and $O \subseteq W$ an obstacle set. The obstacle region is $\mathcal{C}_{\mathrm{obs}}(A, O) = \{ q \in C : A(q) \cap O \neq \emptyset \}$ (touching an obstacle counts as a collision), and the free space is its complement $\mathcal{C}_{\mathrm{free}}(A, O) = C \setminus \mathcal{C}_{\mathrm{obs}}(A, O)$.

With no obstacles the free space is all of $C$: $\mathcal{C}_{\mathrm{free}}(A, \emptyset) = C$.
