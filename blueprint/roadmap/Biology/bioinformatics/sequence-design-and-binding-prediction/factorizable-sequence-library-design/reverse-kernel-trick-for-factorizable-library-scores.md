# Reverse kernel trick for factorizable library scores

Fix a finite alphabet $\Sigma$ and lengths $L_p + L_s = L$. For sets of prefixes $X \subseteq \Sigma^{L_p}$ and suffixes $Y \subseteq \Sigma^{L_s}$, the **factorizable library** $X \oplus Y = \{x \oplus y : x \in X, y \in Y\}$ consists of all concatenations, so it has $|X|\,|Y|$ members while only $|X| + |Y|$ segments are synthesised. Let $f : \Sigma^L \to \mathbb R$ score single sequences. If there are feature maps $\varphi_p : \Sigma^{L_p} \to V$ and $\varphi_s : \Sigma^{L_s} \to V$ into an inner-product space with $f(x \oplus y) = \langle \varphi_p(x), \varphi_s(y) \rangle$, then the total library score factorises as

$$\sum_{x \in X} \sum_{y \in Y} f(x \oplus y) = \Big\langle \sum_{x \in X} \varphi_p(x),\ \sum_{y \in Y} \varphi_s(y) \Big\rangle .$$

Maintaining the two running sums, a change of one prefix or one suffix updates the total score with one vector update and one inner product, instead of re-scoring the $\max(|X|, |Y|)$ affected library members.

For a pairwise (Potts) score $f(z) = \sum_{k} h_k(z_k) + \sum_{k < l} J_{kl}(z_k, z_l)$, finite-dimensional features exist with dimension $L_s |\Sigma| + 2$: index coordinates by suffix positions $l$ and letters $b$, set $\varphi_p(x)_{(l,b)} = \sum_{k \le L_p} J_{k,L_p+l}(x_k, b)$ and $\varphi_s(y)_{(l,b)} = \mathbf 1[y_l = b]$, and add two coordinates carrying the prefix-only part $g_p(x)$ (paired with the constant $1$) and the suffix-only part $g_s(y)$ (paired with the constant $1$).

## Proof sketch

The factorisation is bilinearity of the inner product. The name reverses the kernel trick, which replaces an explicit inner product of features by a kernel evaluation; here an expensive function of a concatenation is replaced by an inner product of cheap segment features. For the Potts case, cross terms between a prefix position $k$ and a suffix position $l$ are linear in the one-hot encoding of the suffix, so they collect into $\langle \varphi_p(x), \varphi_s(y) \rangle$, while terms internal to one segment ride on constant coordinates. For general scores, Dai et al. learn the two feature maps as a pair of neural networks trained so that their inner product approximates a sequence model. Their design method (stochastically annealed product spaces, SAPS) runs Gibbs sweeps with simulated annealing over all positions of all segments, scoring each proposal by this inner product plus a position-wise entropy term for diversity; the cost per sweep scales with $|X| + |Y|$ rather than $|X|\,|Y|$. They also show that, under standard complexity assumptions, no efficient algorithm can reliably design a factorizable library appreciably better than a random one, which motivates the heuristic.

## Sources

- Z. Dai, S. D. Saksena, G. Horny, C. Banholzer, S. Ewert, D. K. Gifford, "Ultra-high-diversity factorizable libraries for efficient therapeutic discovery", Genome Research 32 (2022), 1787–1794, <https://doi.org/10.1101/gr.276593.122> (PMC9528983), Methods, "Preliminaries", "SAPS generates factorizable libraries" and "The reverse kernel trick allows for efficient library score evaluation".
