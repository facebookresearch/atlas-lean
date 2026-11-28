# Empirical Bayes marginal reconstruction integrated over topologies

**Setting.** $d$ is an alignment column (the observed states at the leaves), $m$ a substitution model with equilibrium frequencies $\pi$, $t$ a tree topology with branch lengths and model parameters $\theta$. For an ancestral node, defined on every topology as the most recent common ancestor of a fixed set of descendant taxa, let $L(d \mid a, m, t, \theta)$ be the conditional likelihood of $d$ given state $a$ at that node.

**Marginal (empirical Bayes) reconstruction on one tree.** With $\hat\theta_t$ the maximum-likelihood parameters on $t$,

$$\Pr(a \mid d, m, t, \hat\theta_t) = \frac{\pi_a\, L(d \mid a, m, t, \hat\theta_t)}{\sum_{b} \pi_b\, L(d \mid b, m, t, \hat\theta_t)} \qquad \text{(Eq. 1)},$$

the sum running over the 4 nucleotides or 20 amino acids. The reconstructed state is the one with the largest posterior probability; on the ML topology this is the usual "ML method".

**Topological empirical Bayes (TEB).** Integrating over a set of topologies,

$$\Pr_{\mathrm{TEB}}(a \mid d, m) = \sum_{t} P_{\mathrm{EB}}(t \mid D)\,\Pr(a \mid d, m, t, \hat\theta_t) \qquad \text{(Eq. 2)},$$

where $P_{\mathrm{EB}}(t \mid D) \propto \Pr(t)\,L(D \mid t, \hat\theta_t)$ is the empirical Bayes posterior of $t$ given the whole alignment $D$, using the ML parameters on each tree. This is equivalent to the fully Bayesian expression that averages ancestral-state posteriors over the tree posterior (Eq. 3).

**Robustness.** In simulations with both simple four-taxon and empirically derived uncertainty, TEB and ML reconstructions almost always choose the same state and have the same accuracy: sites whose ancestral state differs between plausible trees are those that carry strong phylogenetic signal, so they also make the tree posterior concentrated.

## Depends on

- [Pupko's reconstruction is a joint maximum-likelihood reconstruction](pupko-is-joint-ml.md)

## Expansion

Eq. 1 is Bayes' theorem at one node with the equilibrium distribution as prior: $L(d \mid a, \dots)$ is computed by Felsenstein pruning with the node's state fixed, and normalizing over $a$ marginalizes the states at all other internal nodes. This differs from joint reconstruction (Pupko's algorithm), which maximizes over all internal states simultaneously. Eq. 2 is the law of total probability over topologies with tree weights from the empirical Bayes posterior. The trade-off reported by the source explains why integration rarely matters: the per-tree posteriors disagree mainly where long branches or short internodes make the column informative about the topology, and then one tree dominates the mixture; where the topology is uncertain, the competing trees imply the same ancestral state.

## Sources

- V. Hanson-Smith, B. Kolaczkowski, J. W. Thornton, "Robustness of ancestral sequence reconstruction to phylogenetic uncertainty", Molecular Biology and Evolution 27(9) (2010) 1988–1999, section "Ancestral State Reconstruction Algorithms" (Eqs. 1–3) and section "An Intrinsic Trade-off Explains Why Incorporating Uncertainty Does Not Affect ASR", <https://doi.org/10.1093/molbev/msq081> (PMC2922618).
- Z. Yang, S. Kumar, M. Nei, "A new method of inference of ancestral nucleotide and amino acid sequences", Genetics 141 (1995) 1641–1650.
