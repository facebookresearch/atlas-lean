# Obstacle region of a union of obstacles

Let $C$ be a set of configurations, $W$ a workspace, $A : C \to \mathcal{P}(W)$ a placement assigning to each configuration the set of workspace points occupied by the body, and $O \subseteq W$ an obstacle set. The obstacle region is $\mathcal{C}_{\mathrm{obs}}(A, O) = \{ q \in C : A(q) \cap O \neq \emptyset \}$ (touching an obstacle counts as a collision), and the free space is its complement $\mathcal{C}_{\mathrm{free}}(A, O) = C \setminus \mathcal{C}_{\mathrm{obs}}(A, O)$.

For obstacle sets $O, O' \subseteq W$,

$$\mathcal{C}_{\mathrm{obs}}(A, O \cup O') = \mathcal{C}_{\mathrm{obs}}(A, O) \cup \mathcal{C}_{\mathrm{obs}}(A, O') .$$
