# Strong barbed bisimilarity

Strong barbed bisimilarity on π-calculus processes is the strong bisimilarity of the [decorated reduction system](observed-lts.md): the largest relation $R$ such that whenever $P \mathrel{R} Q$, every transition of $P$ is matched by a transition of $Q$ with the same label and $R$-related targets, and conversely. Equivalently ([characterization](is-bisimulation-observed-lts-iff.md)), reductions are matched one for one and related processes have the same [barbs](barb.md). The relation is not required to be closed under contexts.
