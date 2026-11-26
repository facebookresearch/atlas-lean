# Kőnig's lemma for inverse systems

Let $\alpha_0, \alpha_1, \alpha_2, \dots$ be nonempty sets with $\alpha_0$ finite, and for $i \le j$ let $\pi_{ij} : \alpha_j \to \alpha_i$ be maps such that $\pi_{ii}$ is the identity and $\pi_{ij} \circ \pi_{jk} = \pi_{ik}$ whenever $i \le j \le k$. If every element of every $\alpha_i$ is the image under $\pi_{i, i+1}$ of only finitely many elements of $\alpha_{i+1}$, then there are elements $f_i \in \alpha_i$, one for each $i$, with $\pi_{ij}(f_j) = f_i$ whenever $i \le j$.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577, `exists_seq_forall_proj_of_forall_finite`, <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577/Mathlib/Order/KonigLemma.lean#L108-L112>.
