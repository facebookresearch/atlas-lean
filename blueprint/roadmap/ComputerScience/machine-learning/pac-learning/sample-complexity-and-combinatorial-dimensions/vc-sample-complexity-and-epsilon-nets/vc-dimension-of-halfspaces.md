# VC dimension of halfspaces

Let $X$ be a set and $F$ a vector subspace of the real functions $\mathbb{R}^X$, and let $\mathcal{P}_F = \{x \mapsto [f(x) > 0] : f \in F\}$ be the class of sets on which some $f \in F$ is positive. Then $\mathrm{VCdim}(\mathcal{P}_F) = \dim F$. In particular:

1. homogeneous halfspaces $x \mapsto [\langle w, x\rangle > 0]$, $w \in \mathbb{R}^d$, on $\mathbb{R}^d$ have VC dimension $d$ (the standard basis is shattered);
2. affine halfspaces $x \mapsto [\langle w, x\rangle + b > 0]$, $(w, b) \in \mathbb{R}^{d+1}$, have VC dimension $d+1$ (the origin and the standard basis are shattered).

## Proof sketch

If $n$ points $x_1, \dots, x_n$ are shattered, the $n \times 2^n$ matrix of values $f_j(x_i)$ of functions realizing all sign patterns has rank $n$: a nonzero $\nu$ with $\nu^\top B = 0$ is impossible, because the column whose signs match those of $\nu$ has positive inner product with $\nu$. So $n$ linearly independent functions of $F$ exist and $\dim F \ge n$. Conversely, if $f_1, \dots, f_n \in F$ and points $x_1, \dots, x_n$ make the matrix $(f_j(x_i))$ invertible, every sign pattern $\varepsilon$ is realized by solving $A v = \varepsilon$, so the points are shattered.

The following parametrized form is derived here and is not stated in this form in the cited sources. For a linear map $\Phi : V \to \mathbb{R}^X$ from a finite-dimensional real vector space, the class $\{x \mapsto [\Phi(v)(x) > 0] : v \in V\}$ is $\mathcal{P}_F$ for $F = \Phi(V)$, so no set of more than $\dim \Phi(V) \le \dim V$ points is shattered; if some $\dim V$ points $x_1, \dots, x_n$ make $v \mapsto (\Phi(v)(x_j))_j$ surjective onto $\mathbb{R}^n$, then $\dim \Phi(V) = \dim V$ and the VC dimension is $\dim V$. Items 1 and 2 are the cases $F = \{x \mapsto \langle w, x\rangle\}$ and $F = \{x \mapsto \langle w, x\rangle + b\}$, of dimensions $d$ and $d + 1$.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- E. D. Sontag, "VC Dimension of Neural Networks", in C. M. Bishop (ed.), Neural Networks and Machine Learning, Springer, 1998, pp. 69-95, Section 2, equation (6), and Section 3, Theorem 1.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Section 9.1.3, Theorems 9.2 and 9.3.
