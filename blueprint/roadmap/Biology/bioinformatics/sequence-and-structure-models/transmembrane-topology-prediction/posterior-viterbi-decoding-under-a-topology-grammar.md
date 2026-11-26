# Posterior-Viterbi decoding of label sequences under a topology grammar

**Setting.** A hidden Markov model (or dynamic Bayesian network) for a protein sequence $o = o_1 \dots o_N$ has hidden states $s_i$ from a finite set, each mapped to a topology label $\ell(s_i)$ (for example signal peptide, cytoplasmic, membrane helix, non-cytoplasmic). Several states share a label (sub-regions with different emission or duration models), and the allowed state transitions define a **grammar** of admissible label sequences (a membrane segment must separate cytoplasmic and non-cytoplasmic loops, a signal peptide can only occur at the N-terminus, and so on). The goal is the most probable label sequence

$$\lambda^* = \arg\max_{\lambda} \Pr(\lambda \mid o) = \arg\max_\lambda \sum_{s : \ell(s) = \lambda} \Pr(s \mid o),$$

which is intractable in general because many state paths map to one label sequence; the Viterbi path $s^* = \arg\max_s \Pr(s \mid o)$ need not induce $\lambda^*$.

**Two-stage decoder.**

1. Compute the posterior label marginals $\pi_i(a) = \Pr(\ell(s_i) = a \mid o)$ by the forward–backward algorithm, marginalizing all other hidden variables.
2. Find the admissible path maximizing the product of these marginals:

$$\hat\lambda = \arg\max_{s \text{ admissible}} \prod_{i=1}^{N} \pi_i\big(\ell(s_i)\big),$$

by a Viterbi recursion over the grammar's transition graph in which transition probabilities are replaced by $0/1$ admissibility indicators and emissions by $\pi_i$.

**Properties.**

1. $\hat\lambda$ always obeys the grammar, whereas labelling each position by $\arg\max_a \pi_i(a)$ (posterior decoding) can produce inadmissible sequences.
2. Equivalently, $\hat\lambda$ maximizes $\sum_i \log \pi_i(\ell(s_i))$ over admissible paths, and it coincides with position-wise posterior decoding whenever the position-wise maximizers already form an admissible sequence. (Replacing $\log \pi_i$ by $\pi_i$ in the sum gives the optimal-accuracy decoder, which maximizes the expected number of correctly labelled positions.)
3. Confidence measures follow from the same marginals: the protein-type posterior (globular, signal peptide plus globular, transmembrane, signal peptide plus transmembrane) from a summary variable propagated to the last position, a per-segment score equal to the mean of $\pi_i$ over the segment for its assigned label, and a topology score equal to the minimum segment score over membrane and terminal segments.

## Depends on

- [Viterbi value of a sequence under a profile HMM](../../sequence-alignment/profile-hidden-markov-models/viterbi.md)

## Expansion

Stage 1 is standard inference; summing state posteriors within each label class gives $\pi_i$. Stage 2 is a longest-path problem in a layered graph whose layer $i$ contains the states, with weight $\log \pi_i(\ell(s))$ on nodes and edges allowed only by the grammar, so dynamic programming solves it in $O(N \cdot |\text{edges}|)$ time. Because the posterior marginals already contain the effects of emission, transition and duration probabilities, stage 2 needs none of them. In a dynamic Bayesian network both stages are expressed by modifying the graph: stage 2 attaches to each position an observed child (virtual evidence) whose conditional probability given the state is $\pi_i(\ell(s))$. Experimental knowledge (known protein type, terminus location, or segment positions) enters as additional evidence clamping the corresponding variables. The decoder is the same idea as posterior-Viterbi and optimal-accuracy decoding for $\beta$-barrel membrane proteins and homology-informed prediction.

## Sources

- Reynolds SM, Käll L, Riffle ME, Bilmes JA, Noble WS, "Transmembrane topology and signal peptide prediction using dynamic bayesian networks" (2008), Methods, "Decoding" and "Confidence Scores", and Background, "Virtual evidence", <https://doi.org/10.1371/journal.pcbi.1000213>, PMCID PMC2570248.
