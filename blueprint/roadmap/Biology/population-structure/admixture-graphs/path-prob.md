# Probability of a root-ward path in an admixture graph

In an [admixture graph](admixture-graph.md) with admixture proportions $a$, the probability of a finite sequence of nodes $(v_0, v_1, \dots, v_k)$ is

$$\prod_{i=0}^{k-1} a(v_i, v_{i+1}),$$

which is $1$ for the empty sequence and for sequences of one node.
