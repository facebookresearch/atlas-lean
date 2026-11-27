# Amenability and unitarizability of arbitrary discrete groups

A discrete group $G$ admits a complex-linear mean $m$ on bounded complex functions, normalized by $m(1)=1$, nonnegative real on pointwise nonnegative real functions and invariant under $f(x)\mapsto f(g^{-1}x)$, if and only if every uniformly operator-norm-bounded representation $\pi$ of $G$ on a complete complex Hilbert space is similar by a bounded invertible operator to an isometric representation. Isometric here means $\|S\pi(g)S^{-1}x\|=\|x\|$ for all $g,x$; each operator is invertible because this is a group representation. There is no countability assumption on $G$. The Hilbert-space universe can dominate the group universe, as in the comparator.

## Depends on
The positive complex invariant-mean condition and uniformly bounded group homomorphisms into the algebra of bounded Hilbert-space operators.

## Proof depends on
- [Near-isometric nonunitarizable witnesses](near-isometric-nonamenable-witness.md), for the nonamenable direction.

The amenable direction needs averaging the inner product with the invariant mean and uniform lower as well as upper norm comparison.

## Expansion
Prove the equivalent positive form is represented by a bounded positive invertible operator and gives a similarity. Record the universes in both the amenability and representation statements rather than imposing countability.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DixmierAllDiscrete.lean#L43-L45) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/251.md).
