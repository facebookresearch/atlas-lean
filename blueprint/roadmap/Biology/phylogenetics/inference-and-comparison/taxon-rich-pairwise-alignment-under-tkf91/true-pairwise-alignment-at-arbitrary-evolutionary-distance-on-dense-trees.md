# True pairwise alignment at arbitrary evolutionary distance on dense trees

**Setting.** Sequences evolve under the two-state TKF91 insertion–deletion–substitution process with rates $\eta,\lambda,\mu$ ($\mu>\lambda$), started at stationarity at the root of a known rooted binary ultrametric tree $T=(V,E,\rho,\mathbf t)$ of depth $h$ with leaves $\ell_1,\dots,\ell_n$ in left-to-right planar order. A pairwise alignment of $\sigma_v,\sigma_w$ is *true* if it places homologous sites (descending from a common ancestral site through substitutions only) in the same column and non-homologous sites in different columns. The **Fitch estimator** of the sequence at the root $z$ of a subtree sets $\hat S_\ell=\{\sigma_\ell\}$ at leaves and $\hat S_v=\hat S_{v_1}\cap\hat S_{v_2}$ if non-empty, else $\hat S_{v_1}\cup\hat S_{v_2}$, and returns a uniform element of $\hat S_z$ (applied to whole sequences as states).

**Theorem.** There is a polynomial-time alignment procedure $A$ such that, for every depth $h>0$ and failure probability $\varepsilon>0$, there exists $t_{\max}=t_{\max}(h,\varepsilon)>0$ (depending also on $\eta,\lambda,\mu$) with the following property: for every such tree with all branch lengths $t_e\le t_{\max}$, given $T$ and all leaf sequences, $A$ outputs a true pairwise alignment of $\sigma_{\ell_1}$ and $\sigma_{\ell_n}$ with probability at least $1-\varepsilon$. The depth $h$, i.e. the evolutionary distance between the two sequences, is arbitrary.

The proof rests on two ingredients along the *backbone* path $x_1=\ell_1,\dots,x_B=\ell_n$ (after sparsifying it so consecutive kept vertices are at distance between $\delta_1$ and $2\delta_1$):

1. *(Deterministic step.)* If every interior backbone sequence is reconstructed exactly and consecutive backbone sequences differ by at most one substitution, insertion or deletion, stepwise alignment along the backbone yields a true alignment of the endpoints.
2. *(Probabilistic step.)* For any length cap $\bar L$ and $\delta_a>0$, short enough branches make the Fitch estimator on each off-backbone subtree exact with probability at least $1-\delta_a$; and the probability that some required event fails is at most $C\,h\,\delta_1\log^2(1/\delta_1)$ with $C$ depending only on $\lambda,\mu,\eta$.

## Depends on

- [Two-state TKF91 insertion–deletion process on a tree](two-state-tkf91-indel-process-on-a-tree.md)

## Expansion

Exact ancestral reconstruction is shown by coupling with a percolation process: an edge is *open* if the sequence does not change along it. For short branches the open cluster of each off-backbone subtree root contains a sufficiently "diluted" binary subtree, on which Fitch's intersection rule recovers the root state, and the presence of a diluted open tree suffices even when other leaves are corrupted. A union bound over the $O(h/\delta_1)$ kept backbone segments, with sequence lengths truncated at $\bar L=O(\log(1/\delta_1))$ using the geometric length tail, controls the probability of two or more mutations within a segment and of reconstruction failure. Choosing $\delta_1$ so that $Ch\delta_1\log^2(1/\delta_1)\le\varepsilon$ and then $t_{\max}$ small finishes the proof. The counterintuitive message is that, unlike two isolated sequences, whose homology becomes unrecoverable as distance grows, a sufficiently taxon-rich known phylogeny makes perfect alignment possible at any depth.

## Sources

- Brandon Legried and Sebastien Roch, "Pairwise sequence alignment at arbitrarily large evolutionary distance", The Annals of Applied Probability 34 (2024), 2714–2732, <https://doi.org/10.1214/23-aap2009>; numbering as in arXiv:2207.12543: Theorem 1, Definition 3, Proposition 1, Lemmas 1–5, Propositions 2–3.
