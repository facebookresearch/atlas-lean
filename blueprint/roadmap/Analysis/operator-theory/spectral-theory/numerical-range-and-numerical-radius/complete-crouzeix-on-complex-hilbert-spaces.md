# Complete Crouzeix bounds for bounded operators on complex Hilbert spaces

For a bounded operator $A$ on an arbitrary complex Hilbert space $H$, write $W=\{\langle x,Ax\rangle:\|x\|=1\}$, with the inner product linear in its second argument, and $K=\overline W$. Use $\sup_S^+\|F\|=\sup(\{0\}\cup\{\|F(z)\|:z\in S\})$. Matrix values use the Euclidean operator norm. The amplification space of size $m$ is the completion of the Hilbert tensor product with $\mathbb C^m$, and matrix-valued evaluation is the sum of scalar evaluations tensored with the matrix units.

If $H\ne0$, $K$ is compact and real-convex and contains $\sigma(A)$. For each $m>0$ and polynomial $F(z)=\sum_{k=0}^d z^k B_k$ of any finite degree, the amplification $F[A]=\sum_k A^k\otimes B_k$ has norm at most $2\sup_W^+\|F\|$. The supremum equals the one on $K$ and is attained there.

For every open $U\supset K$ and every entrywise holomorphic $F:U\to\mathbb C^{m\times m}$ with $m>0$, there is a closed $C^1$ path in $U\setminus K$ on $[0,1]$ with index one on $K$ and zero outside $U$. For each entry $f$, its scalar evaluation equals $(2\pi i)^{-1}\int_0^1 f(\gamma(t))\gamma'(t)(\gamma(t)I-A)^{-1}\,dt$ for every such path. Then $\|F[A]\|\le2\sup_K^+\|F\|$ and the supremum is attained in $K$.

For a square $m$-by-$m$ rational matrix $R$, $m>0$, with each reduced denominator nonzero on $K$, all evaluated denominators are units. Evaluating entries as numerator times inverse denominator gives $\|R[A]\|\le2\sup_K^+\|R\|$, again attained on $K$. Some open $U\supset K$ has entrywise holomorphic $R$ and equality of the two evaluations there.

If $H=0$, $W$ is empty; all polynomial, contour-selected holomorphic and totalized rational evaluations are zero, the referenced suprema over $W$ are zero, and the three inequalities hold. This branch includes $m=0$ and does not assume an admissible contour or pole avoidance. In this model the chosen scalar contour evaluation is zero when no qualifying contour exists. Independently of $H,A$, there is an operator on $\mathbb C^2$ and a degree-at-most-one, size-one matrix polynomial with supremum norm one on its numerical range and amplified operator norm two.

## Depends on

- [Numerical range](numerical-range.md) in the second-argument convention and Hilbert tensor amplification.
- The polynomial, contour-integral and rational evaluation conventions above.

## Proof depends on

- [Finite matrix upper bound](complete-crouzeix-matrix-upper-bound.md) and [finite compression](complete-crouzeix-finite-compression.md).
- Spectral containment, admissible contour existence and independence, passage to a holomorphic neighborhood, and the nilpotent two-dimensional witness.

## Expansion

Develop bounded operator polynomial amplification and its finite compression first. Add contour existence for neighborhoods of the compact convex range and verify resolvent evaluation, then pole avoidance and the rational-to-holomorphic bridge. Give the zero-space branch and the exact sharpness witness their own checks rather than adding a nontriviality assumption to the entire endpoint.

## Sources

- OpenAI, [CrouzeixHilbert comparator, hilbert](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CrouzeixHilbert.lean#L148-L153).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/325.md).
