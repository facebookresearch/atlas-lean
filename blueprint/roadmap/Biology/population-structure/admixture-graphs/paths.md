# Root-ward paths from a node of an admixture graph

In an [admixture graph](admixture-graph.md) with parents $\mathrm{pa}$, the set of root-ward paths from a node $X$ is defined by well-founded recursion: it is $\{(X)\}$ if $X$ has no parent, and otherwise the set of sequences $(X, v_1, \dots, v_k)$ with $(v_1, \dots, v_k)$ a root-ward path from some parent $v_1 \in \mathrm{pa}(X)$. These are the sequences $X = v_0, v_1, \dots, v_k = \rho$ ending at the root with $v_{i+1} \in \mathrm{pa}(v_i)$.
