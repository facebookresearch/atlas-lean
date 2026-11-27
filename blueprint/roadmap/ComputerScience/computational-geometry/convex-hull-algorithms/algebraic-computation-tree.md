# Algebraic computation tree

An *algebraic computation tree* on inputs $x_1, \dots, x_n \in \mathbb{R}$ is a rooted binary tree whose vertices carry instructions. A vertex $v$ with one child computes a value $f_v := f_{v_1} \circ f_{v_2}$ with $\circ \in \{+, -, \times, /\}$, or $f_v := c \circ f_{v_1}$ for a real constant $c$, or $f_v := \sqrt{f_{v_1}}$, where each operand is an input $x_i$ or the value $f_{v_i}$ of an ancestor $v_i$; divisors must be nonzero and square-root arguments nonnegative on every input that reaches $v$. A vertex with two children tests $f_{v_1} > 0$, $f_{v_1} \ge 0$ or $f_{v_1} = 0$ and branches on the outcome. Each leaf is labelled YES or NO. The tree *solves the membership problem* for $W \subseteq \mathbb{R}^n$ if, for every input $x$, the leaf reached is labelled YES exactly when $x \in W$. The *complexity* $C(T)$ is the largest number of vertices on a root-to-leaf path followed by some input, and $C(W)$ is the least complexity of a tree that solves the membership problem for $W$.


## Related topics

- [Algebraic decision tree](algebraic-decision-tree.md)

## Sources

- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Section 2 (the algebraic computation tree model, $\mathrm{cost}(x, T)$, $C(T)$ and $C(W)$)
