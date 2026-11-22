# Head-matching relations are bisimulations

Let $\mathcal{R}$ be a binary relation on protocols such that for all $S \mathrel{\mathcal{R}} T$
the heads $\mathrm{unf}(S)$ and $\mathrm{unf}(T)$ are related by the head match
$\mathcal{H}(\mathcal{R})$ (equal head constructors and metadata, with $\mathcal{R}$-related
payloads and continuations). Then $\mathcal{R}$ is a bisimulation of the protocol-tree transition
system.
