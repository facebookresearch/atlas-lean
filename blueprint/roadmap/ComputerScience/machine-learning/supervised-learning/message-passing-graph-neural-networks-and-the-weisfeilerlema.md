# Message-passing graph neural networks and the Weisfeiler–Leman test

Consider finite graphs with node features from a countable set. The one-dimensional Weisfeiler–Leman test starts
from the node features as colors and, at each iteration, replaces the color of every node by a new color that is
an injective function of its current color and the multiset of its neighbors' colors; it decides that two graphs
are not isomorphic if at some iteration the multisets of node colors of the two graphs differ. Let $\mathcal{A}$ be a message-passing
graph neural network that updates node features by aggregating the multiset of neighbor features and
combining it with the node's own feature, followed by a readout on the multiset of node features.

1. If $\mathcal{A}$ maps two graphs to different embeddings, then the one-dimensional Weisfeiler–Leman test
   decides that they are not isomorphic.
2. If the update has the form $h_v^{(k)} = \varphi\big(h_v^{(k-1)}, f(\{\!\{h_u^{(k-1)} : u \in N(v)\}\!\})\big)$
   with $f$ injective on multisets and $\varphi$ injective, and the readout is injective on multisets, then
   with sufficiently many layers $\mathcal{A}$ maps any two graphs that the Weisfeiler–Leman test
   distinguishes to different embeddings.
3. For a countable feature set and multisets of bounded size there is $f$ such that
   $X \mapsto \sum_{x \in X} f(x)$ is injective, and $h(c, X) = (1+\varepsilon) f(c) + \sum_{x \in X} f(x)$
   is injective for all but countably many $\varepsilon$, in particular for every irrational $\varepsilon$.

Mean and max aggregation are not injective on multisets in general.

## Sources

- K. Xu, W. Hu, J. Leskovec and S. Jegelka, *How powerful are graph neural networks?*, ICLR 2019; arXiv:1810.00826, §2 (the Weisfeiler–Leman test), Lemma 2, Theorem 3, Lemma 5, Corollary 6, Lemma 7 and Corollaries 8–9. <https://arxiv.org/pdf/1810.00826>
