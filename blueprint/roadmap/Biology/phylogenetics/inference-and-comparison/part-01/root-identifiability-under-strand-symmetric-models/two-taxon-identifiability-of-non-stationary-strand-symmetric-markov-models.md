# Two-taxon identifiability of non-stationary strand-symmetric Markov models

**Setting.** Order nucleotides as $A,C,G,T$, so that complementation is the reversal $1\leftrightarrow4$, $2\leftrightarrow3$. A $4\times4$ matrix is *strand-symmetric* if it is invariant under simultaneous complementation of rows and columns, i.e. of the form

$$
M=\begin{pmatrix}\delta&\alpha&\beta&\gamma\\ \zeta&\phi&\eta&\theta\\ \theta&\eta&\phi&\zeta\\ \gamma&\beta&\alpha&\delta\end{pmatrix},
$$

equivalently $M=SMS$ with $S$ the reversal permutation. A probability vector $\pi$ is *compositionally asymmetric* if all entries are positive and $\pi(1)\ne\pi(4)$, $\pi(2)\ne\pi(3)$, $\pi(1)/\pi(4)\ne\pi(2)/\pi(3)$ and $\pi(1)/\pi(4)\ne\pi(3)/\pi(2)$, so that base composition at the root violates Chargaff's second parity rule.

**Lemma.** Consider a two-taxon (cherry) discrete Markov model with root distribution $\pi^m$ at node $m$ and transition matrices $P^{ma},P^{mb}$ to the leaves $a,b$. Put $\Pi^m=\mathrm{diag}(\pi^m)$. Assume

1. $P^{ma}$ and $P^{mb}$ are strand-symmetric,
2. $\pi^m$ is compositionally asymmetric,
3. $P^{ma}$ and $P^{mb}$ are invertible.

Then $\pi^m$, $P^{ma}$ and $P^{mb}$ are uniquely determined by the joint distribution of leaf states $J^{ab}=(P^{mb})^T\Pi^mP^{ma}$, up to one of eight permutations of the states at the hidden node $m$.

A stationary strand-symmetric model is *not* identifiable from two taxa: explicit pairs of distinct stationary models give the same $J^{ab}$.

## Expansion

Strand-symmetric matrices satisfy $P=SPS$, and so do their transposes and inverses. Hence

$$
G:=S\,(J^{ab})^{-1}S\,J^{ab}=(P^{ma})^{-1}\,\mathrm{diag}\Big(\tfrac{\pi^m(1)}{\pi^m(4)},\tfrac{\pi^m(2)}{\pi^m(3)},\tfrac{\pi^m(3)}{\pi^m(2)},\tfrac{\pi^m(4)}{\pi^m(1)}\Big)P^{ma},
$$

an eigendecomposition of a matrix computable from the data whose left eigenvectors are the rows of $P^{ma}$. Compositional asymmetry makes the four eigenvalues distinct, so the rows are determined up to scale, and row sums equal to one fix the scale. Only the order of the rows is lost, restricted to the $8$ orderings that keep $P^{ma}$ strand-symmetric; then $\pi^m=\mathbf 1J^{ab}(P^{ma})^{-1}$ and $P^{mb}$ follow by invertibility. In a stationary strand-symmetric model the (unique) stationary distribution satisfies $\pi=\pi S$, i.e. $\pi(1)=\pi(4)$ and $\pi(2)=\pi(3)$, so compositional asymmetry fails, $G$ has repeated eigenvalues, and identifiability is lost. Non-stationary composition is therefore the key to locating the root: base composition changes along the tree, and the direction of change points to where the process started.

## Sources

- Benjamin D. Kaehler, "Full Reconstruction of Non-Stationary Strand-Symmetric Models on Rooted Phylogenies", arXiv:1610.05057 (2016), Section 3: Definitions 3.1–3.2, Lemma 3.1 and Example 3.1, <https://doi.org/10.48550/arXiv.1610.05057>.
