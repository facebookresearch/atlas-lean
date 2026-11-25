# Message-passing GNNs and 1-WL color refinement

Graphs are finite and simple, with initial node features in a countable set. A $K$-layer aggregation-based
graph neural network computes $h_v^{(0)} = x_v$,
$a_v^{(k)} = \mathrm{AGGREGATE}^{(k)}(\{\!\{ h_u^{(k-1)} : u \in N(v) \}\!\})$ on the multiset of neighbour features,
$h_v^{(k)} = \mathrm{COMBINE}^{(k)}(h_v^{(k-1)}, a_v^{(k)})$, and a graph embedding
$h_G = \mathrm{READOUT}(\{\!\{ h_v^{(K)} \}\!\})$. The 1-dimensional Weisfeiler–Leman test (colour refinement) starts
from $c_v^{(0)} = x_v$ and sets $c_v^{(k)} = \mathrm{HASH}(c_v^{(k-1)}, \{\!\{ c_u^{(k-1)} : u \in N(v) \}\!\})$ with an
injective encoding applied to both graphs at once; it distinguishes two graphs at iteration $k$ if their colour
multisets differ.

## Sources

- How Powerful are Graph Neural Networks? (Xu, Hu, Leskovec, Jegelka, ICLR 2019; arXiv:1810.00826) — arXiv / ICLR 2019, Sec 2 (eqs. 2.1-2.4), Sec 3 (WL test). <https://arxiv.org/pdf/1810.00826>
