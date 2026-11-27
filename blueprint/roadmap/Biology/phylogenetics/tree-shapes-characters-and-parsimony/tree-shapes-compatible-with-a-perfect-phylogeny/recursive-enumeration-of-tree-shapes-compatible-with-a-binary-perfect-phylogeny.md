# Recursive enumeration of tree shapes compatible with a binary perfect phylogeny

**Setting.** Under the infinitely-many-sites mutation model on a coalescent genealogy of $n$ sequences, the observed haplotypes and their frequencies are summarized by a **perfect phylogeny**: a rooted (possibly multifurcating) tree $\pi$ whose $k$ leaves are the distinct haplotypes, labeled by their counts $n_1,\dots,n_k\ge1$ with $\sum_i n_i=n$ (mutation labels discarded); $\Pi_n$ is the set of such trees, and the single node $(n)$ represents a sample with no informative mutations. A binary tree shape $T$ with $n$ leaves is **compatible** with $\pi$, written $T\rightsquigarrow\pi$, if the $k$ leaves of $\pi$ correspond one-to-one to $k$ disjoint subtrees of $T$ of sizes $n_1,\dots,n_k$ and collapsing those subtrees (and internal edges) turns $T$ into $\pi$. For binary perfect phylogenies, $\pi\le\sigma$ (*refinement*) if $\sigma$ arises from $\pi$ by repeatedly collapsing cherries; the **meet** $\pi_1\wedge\pi_2$ is the largest common refinement, set to $\emptyset$ if none exists (in particular if $\pi_1,\pi_2$ have different sample sizes), and the **join** $\pi_1\vee\pi_2$ is the smallest common coarsening.

Let $S_m$ be the number of unranked unlabeled binary tree shapes with $m$ leaves (Wedderburn–Etherington numbers), $R_m$ the number of ranked tree shapes ($R_1=R_2=1$, $R_{m+1}=\tfrac12\sum_{k=0}^{m-1}\binom{m-1}{k}R_{k+1}R_{m-k}$, the Euler zigzag numbers), $L_m=\prod_{i=2}^m\binom i2=\frac{m!(m-1)!}{2^{m-1}}$ ranked labeled trees and $X_m=(2m-3)!!$ unranked labeled trees. Write $G(\pi)$, $G^R(\pi)$ for the numbers of compatible unranked and ranked unlabeled shapes, and $G^L(\pi)$, $G^X(\pi)$ for ranked and unranked labeled trees compatible with a labeled perfect phylogeny; for a single leaf, $G((m))=S_m$, $G^R((m))=R_m$, $G^L((m))=L_m$, $G^X((m))=X_m$.

**Theorem.** $(\Pi_n\cup\{\emptyset\},\wedge,\vee)$ is a lattice with top element $(n)$ and bottom $\emptyset$. For a binary perfect phylogeny $\pi=(\pi_1,\pi_2)$ with $\pi_i\in\Pi_{n_i}$:

$$G(\pi)=\begin{cases}G(\pi_1)G(\pi_2)-\tfrac12\,G(\pi_1\wedge\pi_2)\bigl(G(\pi_1\wedge\pi_2)-1\bigr)&\pi_1\wedge\pi_2\ne\emptyset,\\ G(\pi_1)G(\pi_2)&\pi_1\wedge\pi_2=\emptyset,\end{cases}$$

$$G^R(\pi)=\begin{cases}\binom{2n_1-2}{n_1-1}\Bigl(G^R(\pi_1)G^R(\pi_2)-\tfrac12\,G^R(\pi_1\wedge\pi_2)^2\Bigr)&\pi_1\wedge\pi_2\ne\emptyset,\\ \binom{n_1+n_2-2}{n_1-1}G^R(\pi_1)G^R(\pi_2)&\pi_1\wedge\pi_2=\emptyset,\end{cases}$$

and for labeled perfect phylogenies (whose two root subtrees carry disjoint sets of sequences)

$$G^L(\pi)=\binom{n_1+n_2-2}{n_1-1}G^L(\pi_1)G^L(\pi_2),\qquad G^X(\pi)=G^X(\pi_1)G^X(\pi_2).$$

In particular, for a cherry $(n_1,n_2)$: $G=S_{n_1}S_{n_2}$ and $G^R=\binom{n_1+n_2-2}{n_1-1}R_{n_1}R_{n_2}$ if $n_1\ne n_2$, and $G=\tfrac12S_{n_1}(S_{n_1}+1)$, $G^R=\tfrac12\binom{2n_1-2}{n_1-1}R_{n_1}^2$ if $n_1=n_2$.

## Expansion

A compatible tree splits at its root into a tree compatible with $\pi_1$ and one compatible with $\pi_2$. When the meet is empty these sets are disjoint and the count is a product (times the $\binom{n_1+n_2-2}{n_1-1}$ interleavings of the two subtrees' internal-node ranks in the ranked case). When the meet is non-empty (so $n_1=n_2$), unordered pairs of root subtrees are overcounted exactly on pairs of distinct shapes both compatible with $\pi_1\wedge\pi_2$; splitting into the cases "same perfect phylogeny", "one refines the other" and "incomparable" and summing yields the correction terms. Example: $G((4,2))=S_4S_2=2$, $G(((4,2),6))=2\cdot6-\tfrac12\cdot2\cdot1=11$, and $G^R(((4,2),6))=\binom{10}{5}(8\cdot16-\tfrac12\cdot 8^2)=24{,}192$. These counts give the size of the latent tree space a coalescent sampler must explore conditional on the observed mutation pattern.

## Sources

- Julia A. Palacios, Anand Bhaskar, Filippo Disanto and Noah A. Rosenberg, "Enumeration of binary trees compatible with a perfect phylogeny", Journal of Mathematical Biology 84 (2022), 54, <https://doi.org/10.1007/s00285-022-01748-w>; numbering as in arXiv:2108.04849: Section 3: Definition 1, Theorem 4, Definitions 5 and 8, Propositions 6, 7, 9, 10, 13, 16.
