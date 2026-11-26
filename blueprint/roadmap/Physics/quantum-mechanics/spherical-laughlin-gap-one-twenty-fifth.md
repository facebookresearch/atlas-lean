# Spherical Laughlin gap bound with coefficient one twenty-fifth

For integers $N\geq2$ and flux $Q=3(N-1)$, let $\psi$ be an antisymmetric complex tensor on $\{0,\ldots,Q\}^N$. At each particle pair $i<j$ and index $0\leq p<2Q-1$, form its contraction in positions $i,j$ against $b_{Qp}(x,y)$, which is zero except when $x+y=p+1$, and otherwise is $(x-y)\sqrt{[Q]_x[Q]_y p!/(Q[2Q-2]_p x!y!)}/\sqrt2$. Here $[m]_k$ is the falling factorial. Let $\mathcal E_Q(\psi)$ be the sum of the squared norms of all these contractions over the remaining particle indices. The vector $L_Q$ has component at $a$ equal to the coefficient of $\prod_i u_i^{Q-a_i}v_i^{a_i}$ in $\prod_{i<j}(u_iv_j-u_jv_i)^3$, divided by $\prod_i\sqrt{\binom Q{a_i}}$. Then for some $N_0\geq2$ and every $N\geq N_0$, $\mathcal E_Q(\psi)\geq(1/25)\inf_{c\in\mathbb C}\sum_a|\psi(a)-cL_Q(a)|^2$ for every such $\psi$.

## Depends on
The specified spherical coefficient and antisymmetry conventions, with coefficient one for each pair projector.

## Proof depends on

- [Spherical Fock-space inequality](spherical-laughlin-fock-operator-gap.md), since $1/25$ is strictly below the Fock constant after matching sectors.

The sector kernel is exactly the spherical Laughlin line. Its proof uses the normalized tensor-to-occupation transfer and polynomial pair-cube divisibility at flux $3(N-1)$.

## Expansion

Prove the norm and energy transport separately from the polynomial kernel identification. For the latter, use the equivalence between zero pair energy and divisibility by the pair brackets cubed, together with the exact degree constraint and nonzero Laughlin vector. Apply the linked Fock inequality and spectral restriction to get the squared distance from that identified line.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LaughlinGap.lean#L78-L80) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/269.md).
