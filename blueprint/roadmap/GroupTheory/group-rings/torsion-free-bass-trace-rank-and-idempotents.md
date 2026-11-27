# Trace and augmentation rank for torsion-free group rings

Let $G$ be any group with no nonidentity element of finite order. For every positive matrix size, a complex group-ring idempotent matrix has sum of the identity coefficients of its diagonal entries equal to the rank of its augmented complex matrix (augmentation sums all coefficients). On algebraic $K_0(\mathbb C[G])$ the resulting trace equals the integral augmentation rank viewed in $\mathbb C$, and its range is exactly $\mathbb Z\subset\mathbb C$.

Here the matrix presentation of $K_0$ has generators all finite idempotent matrices and relations for block direct sum and for $ab$ and $ba$ both idempotent with $a,b$ rectangular. In addition, for every commutative domain $R$ of characteristic zero, a scalar idempotent of $R[G]$ equals $0$ or $1$. No uniform bound on the supports is used.

## Depends on

- Matrix-idempotent $K_0$, augmentation rank, identity coefficient and ordinary torsion-freeness.

## Proof depends on

- [Complex trace vanishing](complex-bass-trace-support.md), the comparison of the module and matrix traces, and the transfer to characteristic-zero coefficient domains.

## Expansion

Use the trace support theorem to identify the augmented trace with the identity coefficient. Generate the integral range by the identity idempotent and its virtual negatives. For scalar idempotents transport the finitely many coefficients into a complex model and use faithfulness of the positive regular trace on projections.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BassTorsionFree.lean#L297-L308) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BassTorsionFree.lean).
