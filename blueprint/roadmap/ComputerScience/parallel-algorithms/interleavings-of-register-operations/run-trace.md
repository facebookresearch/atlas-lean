# Running an interleaved register trace

Given an initial register value $\mathit{init} \in \mathbb{N}$ and a trace $[(t_1, o_1), \dots, (t_k, o_k)]$ of thread-tagged operations, the run applies the operations from left to right and ignores the thread tags:

$$\mathrm{runTrace}(\mathit{init}, [(t_1,o_1),\dots,(t_k,o_k)]) = \mathrm{apply}(\cdots \mathrm{apply}(\mathrm{apply}(\mathit{init}, o_1), o_2) \cdots, o_k).$$

The empty trace returns $\mathit{init}$.
