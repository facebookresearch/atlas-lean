# VC dimension of halfspaces

Let $V$ be a finite-dimensional real vector space and $\Phi : V \to \mathbb{R}^X$ a linear map from parameters to real functions on a set $X$, and let $\mathcal{P}_\Phi = \{x \mapsto [\Phi(v)(x) > 0] : v \in V\}$. Then no set of more than $\dim V$ points is shattered by $\mathcal{P}_\Phi$; if moreover some $\dim V$ distinct points $x_1, \dots, x_n$ have the property that $v \mapsto (\Phi(v)(x_j))_j$ is surjective onto $\mathbb{R}^n$, then $\mathrm{VCdim}(\mathcal{P}_\Phi) = \dim V$. In particular:

1. homogeneous halfspaces $x \mapsto [\langle w, x\rangle > 0]$, $w \in \mathbb{R}^d$, on $\mathbb{R}^d$ have VC dimension $d$ (the standard basis is shattered);
2. affine halfspaces $x \mapsto [\langle w, x\rangle + b > 0]$, $(w, b) \in \mathbb{R}^{d+1}$, have VC dimension $d+1$ (the origin and the standard basis are shattered).

## Proof sketch

If $n > \dim V$ points were shattered, the evaluation functionals $v \mapsto \Phi(v)(x_j)$ would be linearly dependent: $\sum_j a_j \Phi(v)(x_j) = 0$ for some nonzero $a$. Label $x_j$ positive exactly when $a_j > 0$; a parameter realizing this labeling makes the sum strictly positive (after possibly negating $a$), a contradiction. Surjectivity at $\dim V$ points realizes every sign pattern.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
