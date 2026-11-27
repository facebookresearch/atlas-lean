# Relabeling the class prior permutes the labeling

Let $V$ be a finite vertex set, $K$ a finite set of classes, $p \in \mathbb{R}^K$ real class weights, $z : V \to K$ a labeling and $\sigma$ a permutation of $K$. The prior weight $\prod_v p_{\sigma(z(v))}$ of $z$ under the relabeled weights $p \circ \sigma$ equals the prior weight of the labeling $\sigma \circ z$ under $p$. No condition on $p$ is needed; for a probability vector $p$ these are the probabilities of the labelings.
