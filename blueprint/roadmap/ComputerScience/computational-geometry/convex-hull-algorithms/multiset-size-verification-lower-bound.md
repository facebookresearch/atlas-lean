# Lower bound for multiset size verification

Fix $d \ge 1$. In the *multiset size verification* problem the input is $z = (z_1, \dots, z_n) \in \mathbb{R}^n$ together with an integer $1 \le k \le n$, and the answer is yes when the multiset $\{z_1, \dots, z_n\}$ has exactly $k$ distinct elements. There are constants $c_d > 0$ and $k_d \ge 2$, depending only on $d$, such that for all $n \ge k \ge k_d$ every $d$-th order algebraic decision tree that decides the set of yes-inputs $\{z \in \mathbb{R}^n : |\{z_1, \dots, z_n\}| = k\}$ has height at least $c_d \, n \log_2 k$; that is, the height is $\Omega(n \log k)$.

## Depends on

- [Algebraic decision tree](algebraic-decision-tree.md)

## Proof depends on

- [Ben-Or's lower bound for algebraic decision trees](ben-or-s-lower-bound-for-algebraic-decision-trees.md)

## Sources

- D. G. Kirkpatrick and R. Seidel, "The ultimate planar convex hull algorithm?", *SIAM Journal on Computing* 15(1) (1986), 287–299, <https://doi.org/10.1137/0215021>: Section 5, Corollary 5.1 (multiset size verification needs $\Omega(n \log k)$ steps), whose proof shows that the yes-set has at least $\max\{k^{n-k}, k!\}$ connected components, with Ben-Or's Theorem 8 as Theorem 5.1
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the lemma that the MSV problem requires $\Omega(n \log k)$ steps in the $d$-th order algebraic decision tree model, by exhibiting $k!\,k^{n-k}$ connected components
