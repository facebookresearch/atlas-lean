# Local actions

Let $(\Sigma, \bullet, u)$ be a [separation algebra](separation-algebras.md). $P(\Sigma)^\top$ is the powerset of $\Sigma$ with a new greatest element $\top$, standing for a memory fault; the separating conjunction extends to it by $p \ast \top = \top \ast p = \top$, keeping the unit $\mathrm{emp}$. For predicates $p, q \subseteq \Sigma$ and a function $f : \Sigma \to P(\Sigma)^\top$, the *semantic Hoare triple* $\langle\!\langle p \rangle\!\rangle\, f\, \langle\!\langle q \rangle\!\rangle$ holds if $f\sigma \sqsubseteq q$ for every $\sigma \in p$; it is fault-avoiding, since $\top \not\sqsubseteq q$, and the empty set stands for divergence. A *local action* is a function $f : \Sigma \to P(\Sigma)^\top$ satisfying the locality condition

$$\sigma_1 \# \sigma_2 \implies f(\sigma_1 \bullet \sigma_2) \sqsubseteq (f\sigma_1) \ast \{\sigma_2\}.$$

Local actions are ordered pointwise. In the heap model, heap mutation, allocation and disposal are local actions, while the function setting every allocated cell to $0$ is not.

## Depends on

- [Separation algebras](separation-algebras.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 3, Definitions 5, 6 and 8, the remarks before them, and Example 1 after Lemma 11.
