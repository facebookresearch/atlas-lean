# Rebuilding restores the congruence invariant

Let a finite [e-graph](e-graphs.md), with finitely many e-class ids and e-nodes, satisfy the congruence and hashcons invariants, and then be modified by $\mathrm{add}$ and $\mathrm{merge}$ operations that do not restore the [congruence invariant](congruence-and-hashcons-invariants-of-e-graphs.md), while every merged e-class is recorded on a worklist $W$. *Rebuilding* repeatedly removes an e-class $c$ from $W$, canonicalizes the e-nodes that have a child in $c$, merges each pair of them that has become congruent, and adds the merged e-classes to $W$, until $W$ is empty. Rebuilding terminates, and on termination $\equiv_{\mathrm{node}} = \cong^*$.

**Proof idea.** Rebuilding merges only congruent e-nodes, so the congruence closure $\cong^*$ does not change while $\equiv_{\mathrm{node}}$ grows. Let $I = (\cong^*) \setminus (\equiv_{\mathrm{node}})$, a finite set. Each repair step either merges a congruent pair, decreasing $|I|$ while possibly enlarging $W$, or finds no such pair and decreases $|W|$; so the pair $(|I|, |W|)$ decreases lexicographically. When $W$ is empty, every e-class whose parents had to be checked has been checked, as in upward merging, and $I$ is empty.

## Depends on

- [Congruence and hashcons invariants of e-graphs](congruence-and-hashcons-invariants-of-e-graphs.md)
- [E-graphs](e-graphs.md)

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", *Proceedings of the ACM on Programming Languages* 5(POPL), Article 23, 2021, doi:10.1145/3434304, author copy arXiv:2004.03082v3 <https://arxiv.org/abs/2004.03082>, Section 3: upward merging (Section 3.1), the rebuild and repair procedures of Figure 4 (Section 3.2), and Theorem 3.1 with its proof, which appeals to G. Nelson's thesis, *Techniques for program verification*, Stanford University, 1980, Chapter 7, for the final step.
