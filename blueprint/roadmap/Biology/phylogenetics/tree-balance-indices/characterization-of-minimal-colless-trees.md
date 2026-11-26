# Characterization of minimal Colless trees

For $n \ge 2$ let $c_n$ be the [minimum Colless index](minimum-colless-index.md) on $n$ leaves, and define the set of **admissible root splits**

$$QB(n) = \{(n_a, n_b) \in \mathbb N^2 : n_a \ge n_b \ge 1,\ n_a + n_b = n,\ c_{n_a} + c_{n_b} + n_a - n_b = c_n\}.$$

It is nonempty, since $(\lceil n/2 \rceil, \lfloor n/2 \rfloor) \in QB(n)$. A tree with $n$ leaves is a **minimal Colless tree** if its Colless index equals $c_n$.

**Proposition.** Let $T = (T_a, T_b)$ be a bifurcating tree with $n \ge 2$ leaves, $T_a$ with $n_a$ leaves and $T_b$ with $n_b$ leaves, $n_a \ge n_b$. The following are equivalent:

1. $T$ is a minimal Colless tree.
2. $T_a$ and $T_b$ are minimal Colless trees and $(n_a, n_b) \in QB(n)$.
3. For every internal node $v$ of $T$ with children $v_1, v_2$ ordered so that $\kappa_T(v_1) \ge \kappa_T(v_2)$, $(\kappa_T(v_1), \kappa_T(v_2)) \in QB(\kappa_T(v))$.

In particular, if $n$ is a power of $2$ the only minimal Colless tree is the fully symmetric tree, and every rooted subtree of a minimal Colless tree is again minimal Colless.

## Depends on

- [Colless index and its root decomposition](colless-index.md)
- [Minimum Colless index](minimum-colless-index.md)

## Expansion

(1) ⇒ (2) uses the root decomposition $C(T) = C(T_a) + C(T_b) + n_a - n_b$: replacing a non-minimal pending subtree by a minimal one strictly lowers $C(T)$, and then $C(T) = c_{n_a} + c_{n_b} + n_a - n_b$ must equal $c_n$. (2) ⇒ (1) is the same identity read backwards, and (2) ⇔ (3) follows by induction on the depth of $v$. The characterization yields a recursive generator of all minimal Colless trees: choose any $(n_a, n_b) \in QB(n)$ and recurse. The paper also lists $QB(n)$ explicitly in terms of the binary expansion of $n$ and shows two extremal members, the maximally balanced tree (greedy from the top) and the greedy-from-the-bottom tree.

## Sources

- T. M. Coronado, M. Fischer, L. Herbst, F. Rosselló and K. Wicke, "On the minimum value of the Colless index and the bifurcating trees that achieve it", *Journal of Mathematical Biology* (2020), <https://doi.org/10.1007/s00285-020-01488-9> (Eqn. (1), Proposition 1, Corollary 1 and Remark 1; numbering as in the arXiv version 1907.05064v2).
