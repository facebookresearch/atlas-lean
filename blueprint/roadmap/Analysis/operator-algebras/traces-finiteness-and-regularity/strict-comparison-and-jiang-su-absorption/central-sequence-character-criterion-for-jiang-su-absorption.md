# Central-sequence character criterion for Jiang–Su absorption

For every nonzero separable unital complex C*-algebra $A$ and every free ultrafilter $\omega$ on $\mathbb N$, form the norm ultrapower $\ell^\infty(A)/\{(a_n):\lim_\omega\|a_n\|=0\}$. Let $F_\omega(A)$ be the relative commutant of the constant copy of $A$. Then every complex-linear multiplicative star map $F_\omega(A)\to\mathbb C$ (not assumed unital) is zero if and only if there is a complex star-algebra isomorphism $A\cong A\otimes_{\min}\mathcal Z$.

Use the following specific inductive-limit model. For adjacent matrix sizes $p,q$, the dimension-drop stage is

$$I_{p,q}=\{f\in C([0,1],M_p(\mathbb C)\otimes M_q(\mathbb C)): f(0)\in M_p(\mathbb C)\otimes 1_q,\ f(1)\in 1_p\otimes M_q(\mathbb C)\}.$$

Start at $p_0=2$ and use $p_{j+1}=p_j^7$ and stages $I_{p_j,p_j+1}$. For $p=p_j$, put $b=(p-1)(p^4+p^2+1)$. The connection to $I_{p^7,p^7+1}$ has $pb+1$ lower, $(p+1)b+1$ upper, and $p(p+1)b^2-1$ constant-middle evaluation blocks. Use the [exact diagonal connecting map, including the eigenpaths, endpoint reindexing and interpolating unitary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CharacterCriterion.lean#L1449-L1602), with one endpoint copy and $b$ middle copies at each end as in the [specified presentation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CharacterCriterion.lean#L2002-L2120). Take the norm completion of the algebraic direct limit with these isometric connecting maps. The tensor norm is the supremum over spatial tensor representations. The spaces in this comparator are small-universe types. Nuclearity, simplicity and trace hypotheses on $A$ are not imposed.

## Depends on

- The bounded-sequence quotient, its relative commutant and the minimal C*-tensor completion.
- The prime-dimension-drop inductive-limit model in the comparator, including its connecting maps.

## Proof depends on

- Identification of the inductive-limit model with the Jiang–Su algebra and the two implications relating its absorption to characters in the actual norm relative commutant.

## Expansion

Isolate the operator-norm quotient and relate it to the native central sequence model. Check the spatial norm and the inductive-limit model before the absorption argument; a comparison with an abstract tensor norm or a tracial ultrapower would not prove this result.

## Sources

- OpenAI, [CharacterCriterion comparator, character_criterion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CharacterCriterion.lean#L2128-L2133).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/299.md).
