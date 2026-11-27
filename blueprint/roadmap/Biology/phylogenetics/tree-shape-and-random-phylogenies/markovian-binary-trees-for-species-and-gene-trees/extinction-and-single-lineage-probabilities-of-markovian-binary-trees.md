# Extinction and single-lineage probabilities of Markovian binary trees

**Markovian binary tree (MBT).** Each branch of a species tree evolves independently through phases $\{1,\dots,n\}$ of a continuous-time Markov chain with an absorbing state, starting from an initial phase distribution $\alpha$. In phase $i$ it changes phase to $j$ at rate $(D_0)_{ij}$, goes extinct at rate $d_i$, and speciates at rate $B_{i,jk}$, moving itself to phase $k$ while the daughter branch starts in phase $j$ (so $B_{i,jk} = (D_1)_{ik}P_{j,ik}$). BiSSE, MuSSE and trait-dependent or geographic speciation models are special cases.

**Extinction probabilities.** Let $E_i(t)$ be the probability that the tree started by one branch in phase $i$ is extinct by time $t$, and $\mathbf E(t) = (E_i(t))$. Then

$$\frac{d\mathbf E(t)}{dt} = \mathbf d + \mathbf D_0\mathbf E(t) + \mathbf B\big(\mathbf E(t)\otimes\mathbf E(t)\big), \qquad \mathbf E(0) = \mathbf 0,$$

and the ultimate extinction vector $\mathbf E = \lim_{t\to\infty}\mathbf E(t)$ is the minimal nonnegative solution of $\mathbf E = (-\mathbf D_0)^{-1}\mathbf d + (-\mathbf D_0)^{-1}\mathbf B(\mathbf E\otimes\mathbf E)$, computable by Newton's method from $\mathbf E_0 = \mathbf 0$.

**Lemma (one surviving lineage).** Let $D^{(1)}_i(t)$ be the probability that a tree started in phase $i$ has exactly one extant lineage at time $t$. Then $\mathbf D^{(1)}(t)$ solves

$$\frac{d\mathbf D^{(1)}(t)}{dt} = \mathbf D_0\mathbf D^{(1)}(t) + \mathbf B\big(\mathbf E(t)\otimes\mathbf D^{(1)}(t)\big) + \mathbf B\big(\mathbf D^{(1)}(t)\otimes\mathbf E(t)\big), \qquad \mathbf D^{(1)}(0) = \mathbf 1,$$

equivalently $\mathbf D^{(1)}(t) = e^{\mathbf D_0t}\mathbf 1 + \int_0^t e^{\mathbf D_0(t-u)}\mathbf B\big(\mathbf E(u)\otimes\mathbf D^{(1)}(u) + \mathbf D^{(1)}(u)\otimes\mathbf E(u)\big)du$.

**Lemma ($n$ surviving lineages).** With $\mathbf D^{(0)}(t) = \mathbf E(t)$, the probability vectors $\mathbf D^{(n)}(t)$ of exactly $n$ extant lineages satisfy

$$\frac{d\mathbf D^{(n)}}{dt} = \mathbf D_0\mathbf D^{(n)} + \mathbf B\big(\mathbf D^{(0)}\otimes\mathbf D^{(n)} + \mathbf D^{(n)}\otimes\mathbf D^{(0)}\big) + \sum_{n_L=1}^{n-1}\mathbf B\big(\mathbf D^{(n_L)}\otimes\mathbf D^{(n-n_L)}\big),\qquad \mathbf D^{(n)}(0) = \mathbb 1\{n=1\}\mathbf 1.$$

For $n \ge 2$ and $n_L = 1, \dots, n-1$, let $N(t)$ be the number of extant lineages at time $t$, $N_L(t)$ the number of them in the left subtree of the reconstructed tree, and $\mathbf D^{(n_L,n)}(t)$ the vector whose $i$-th entry is $\mathbb P(N_L(t) = n_L,\ N(t) = n)$ for a tree started by one branch in phase $i$. Then

$$\frac{d\mathbf D^{(n_L,n)}}{dt} = \mathbf D_0\mathbf D^{(n_L,n)} + \mathbf B\big(\mathbf D^{(0)}\otimes\mathbf D^{(n_L,n)} + \mathbf D^{(n_L,n)}\otimes\mathbf D^{(0)}\big) + \mathbf B\big(\mathbf D^{(n_L)}\otimes\mathbf D^{(n-n_L)}\big),\qquad \mathbf D^{(n_L,n)}(0) = \mathbf 0.$$

## Proof sketch

All equations come from a first-step (backward Kolmogorov) decomposition on the first event of the root branch: a phase change keeps one branch, extinction contributes $\mathbf d$, and a speciation splits the tree into two independent subtrees whose outcomes combine through the Kronecker product. With one surviving lineage, one subtree must survive with a single lineage and the other must go extinct, which gives the two cross terms. These matrix-analytic quantities are the building blocks of reconstructed-tree likelihoods, of gene-tree models with duplication and loss (as quasi-birth-and-death processes), and of the likelihood of reconciling a gene tree with a species tree.

## Sources

- Albert Ch. Soewongsono, Jiahao Diao, Tristan Stark, Amanda E. Wilson, David A. Liberles, Barbara R. Holland and Małgorzata M. O’Reilly, "Matrix-analytic Methods for the Evolution of Species Trees, Gene Trees, and Their Reconciliation", *Methodology and Computing in Applied Probability* 27 (2025), 9, <https://doi.org/10.1007/s11009-025-10135-z>. Preprint version: arXiv:2309.06447 (2023), Section 2 (MBT model) and Lemmas 1–3 (Section 3; the left-subtree equation is (26)), <https://doi.org/10.48550/arXiv.2309.06447>.
