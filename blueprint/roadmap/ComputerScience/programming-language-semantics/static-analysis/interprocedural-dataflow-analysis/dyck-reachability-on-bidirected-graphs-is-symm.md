# Dyck reachability on bidirected graphs is symmetric

In a bidirected $\Sigma_k$-labeled graph, in the sense of [Dyck reachability](dyck-reachability.md), $v$ is Dyck-reachable from $u$ if and only if $u$ is Dyck-reachable from $v$. Hence Dyck reachability is an equivalence relation on the nodes, whose classes are the maximal Dyck SCCs.

**Proof.** Reverse a witness path from $u$ to $v$. By bidirectedness each reversed edge exists and carries the complementary label, so the word of the reversed path is the reversal of the original word with each $\alpha_i$ and $\bar\alpha_i$ exchanged, which lies in $L_k$ again. Reflexivity holds by the empty path, and transitivity because $L_k$ is closed under concatenation.

## Depends on

- [Dyck reachability](dyck-reachability.md)

## Sources

- K. Chatterjee, B. Choudhary and A. Pavlogiannis, "Optimal Dyck reachability for data-dependence and alias analysis", *Proceedings of the ACM on Programming Languages* 2(POPL):30, 2018, <https://arxiv.org/abs/1910.00241>, Section 3.1, Remark 1, attributed there to Q. Zhang, M. R. Lyu, H. Yuan and Z. Su, "Fast algorithms for Dyck-CFL-reachability with applications to alias analysis", PLDI 2013.
