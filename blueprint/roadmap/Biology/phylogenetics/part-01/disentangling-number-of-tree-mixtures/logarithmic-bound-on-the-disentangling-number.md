# Logarithmic bound on the disentangling number of lists of phylogenetic trees

For a finite label set $X$ let $\mathcal T_X$ be the set of unrooted trivalent (binary) leaf-labeled trees on $X$, and for $K \subseteq X$ let $T|_K$ be the induced subtree on $K$ (suppressing degree-two vertices). Let $\mathcal T_{X,r}$ be the set of unordered lists (multisets) $S = (T_1, \dots, T_r)$ of $r$ trees in $\mathcal T_X$, with $S|_K = (T_1|_K, \dots, T_r|_K)$. A set $K$ **disentangles** $S_1 \ne S_2$ if $S_1|_K \ne S_2|_K$; let $d(S_1,S_2)$ be the smallest size of such a $K$. The **disentangling number** is

$$D(r) = \max_{n \in \mathbb N}\ \max_{S_1 \ne S_2 \in \mathcal T_{[n],r}} d(S_1, S_2).$$

The rooted disentangling number $RD(r)$ is defined in the same way for unordered lists of rooted binary trees.

**Theorem.**

1. $RD(r) = 3\big(\lfloor \log_2 r \rfloor + 1\big)$.
2. $D(r) \le RD(r) + 1$, hence

$$3\big(\lfloor \log_2 r \rfloor + 1\big) \le D(r) \le 3\big(\lfloor \log_2 r \rfloor + 1\big) + 1,$$

where the lower bound is due to Humphries. This improves the earlier linear upper bound $D(r) \le 3r$ and determines $D(r)$ up to one; the known exact values are $D(1) = 4$ (quartets determine the tree) and $D(2) = 6$.

**Use in mixture identifiability.** If the tree parameters of $r$-class phylogenetic mixture models are generically identifiable on all $s$-leaf trees for some $s \ge D(r)$, then they are generically identifiable for $r$-class mixtures on trees with any number $t \ge s$ of leaves; so logarithmically many leaves suffice as the base case.

## Expansion

Rooting at a fixed leaf reduces unrooted lists to rooted ones at the cost of one label, giving $D(r) \le RD(r) + 1$. A rooted binary tree is determined by its rooted triples, so a list $S$ is encoded by the nonnegative integer array $u_S = \sum_i e_{T_i}$ in the tensor space indexed by the triple-topologies of all $3$-subsets of $X$, with $\|u_S\|_1 = r$. Let $g = 3(\lfloor \log_2 r\rfloor + 1)$. If two lists agree on every label set of size at most $g$, they have equal marginals on the simplicial complex whose faces are the collections of triples covering at most $g$ labels, so $u_{S_1} - u_{S_2}$ is a nonzero integer vector in the kernel of that marginal map. A theorem of Kahle says such a kernel vector has $1$-norm at least $2^{s}$, where $s$ is the size of the smallest non-face; here $s = \lfloor \log_2 r\rfloor + 2$ (that many disjoint triples), which forces $2r \ge \|u_{S_1} - u_{S_2}\|_1 \ge 2^{\lfloor \log_2 r \rfloor + 2} > 2r$, a contradiction.

## Sources

- Seth Sullivant, "The disentangling number for phylogenetic mixtures", arXiv (2011); Discrete Mathematics 312 (2012). Theorem 2, Proposition 3, Theorem 4, Theorem 5 (Kahle's bound). <https://doi.org/10.48550/arXiv.1107.2880>. Published version: SIAM Journal on Discrete Mathematics 26(2) (2012), 856–859, <https://doi.org/10.1137/110843459>; locators above refer to the arXiv version.
