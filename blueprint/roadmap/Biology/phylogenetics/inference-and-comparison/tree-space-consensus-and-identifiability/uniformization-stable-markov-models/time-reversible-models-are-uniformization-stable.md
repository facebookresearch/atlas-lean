# Time-reversible models are uniformization stable

**Setting.** For a strictly positive distribution $\pi=(\pi_1,\dots,\pi_n)$ let $D(\pi)=\mathrm{diag}(\pi)$. A rate matrix $Q=(q_{ij})$ is time-reversible with respect to $\pi$ if it satisfies detailed balance $\pi_iq_{ij}=\pi_jq_{ji}$, i.e. $D(\pi)Q=Q^TD(\pi)$. Define

$$\mathrm{GTR}_\pi=\{Q\in\mathcal L_n: D(\pi)Q=Q^TD(\pi)\},\qquad \mathrm{GTR}_\pi^+=\mathrm{GTR}_\pi\cap\mathcal L_n^+,$$

and the general time-reversible model $\mathrm{GTR}^+=\bigcup_\pi\mathrm{GTR}_\pi^+$, where $\mathcal L_n$ are the zero row sum matrices and $\mathcal L_n^+$ the rate matrices.

**Lemma.** For any fixed $D\in\mathrm{Mat}_n(\mathbb R)$, $\mathrm{Comm}^T(D)=\{A: DA=A^TD\}$ is a Jordan subalgebra of $\mathrm{Mat}_n(\mathbb R)$. Hence $\mathrm{GTR}_\pi=\mathrm{Comm}^T(D(\pi))\cap\mathcal L_n$ is a Jordan algebra.

**Theorem.**
1. For each $\pi$, $\mathrm{GTR}_\pi^+$ is uniformization stable: $e^{Qt}-I_n\in\mathrm{GTR}_\pi^+$ for all $Q\in\mathrm{GTR}_\pi^+$, $t\ge0$.
2. The general time-reversible model $\mathrm{GTR}^+$ is uniformization stable, and for $n>2$ it is not a linear model.
3. The Tamura–Nei 1993 model is uniformization stable.
4. For a permutation group $G\le S_n$, the $G$-equivariant time-reversible model $\mathrm{TR}_G^+=\bigcup_\pi\mathrm{TR}^+_{(\pi,G)}$ is uniformization stable if and only if each $\mathrm{TR}^+_{(\pi,G)}$ is.

## Depends on

- [Uniformization stability is equivalent to a Jordan algebra](uniformization-stability-is-equivalent-to-a-jordan-algebra.md)

## Expansion

For $A,B\in\mathrm{Comm}^T(D)$, $D(AB+BA)=(A^TB^T+B^TA^T)D=(AB+BA)^TD$, so the Jordan product stays in the set (the ordinary product does not, which is why GTR is not a Lie–Markov model). $\mathrm{GTR}_\pi$ is spanned by its own rate matrices $\hat L_{ij}=\pi_jL_{ij}+\pi_iL_{ji}$, so it is the minimal subspace of the linear model $\mathrm{GTR}_\pi^+$, and the equivalence theorem gives item 1. Item 2 follows because $\mathrm{GTR}^+$ is the union of the uniformization stable models $\mathrm{GTR}_\pi^+$; for $n=2$ every chain is reversible, while for $n>2$ an explicit sum of reversible rate matrices that is a rate matrix but not reversible shows non-linearity. The Tamura–Nei and $G$-equivariant reversible models are cut out of $\mathrm{GTR}_\pi$ by symmetry conditions compatible with the Jordan structure, giving items 3 and 4.

## Sources

- L. Cooper, J. Sumner, "Uniformization stable Markov models and their Jordan algebraic structure", arXiv:2105.03558 (2021), <https://doi.org/10.48550/arXiv.2105.03558>. Section 3 (Lemmas 3.1, 3.2, 3.7; Theorems 3.3, 3.5; Corollary 3.4; Definition 3.6).
