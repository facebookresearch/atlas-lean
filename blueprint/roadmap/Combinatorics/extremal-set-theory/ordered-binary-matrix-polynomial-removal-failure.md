# Failure of polynomial removal for an explicit ordered binary matrix

Use zero-based indices. Define a fixed $66\times66$ matrix $H$ as follows. In its leading $64\times64$ block put $H_{uv}=1_{u\ne v}$ except when $u\ge32$ and $v\ge59$, where use the bit $\lfloor (u-32)/2^{5-(v-58)}\rfloor\bmod 2$. In the top-right two columns put ones only at $(0,64),(1,65)$; in the bottom-left put ones only at $(64,0),(65,1)$. In the bottom-right $2\times2$ block put ones where $u=65$ or $v=64$. A copy chooses independently strictly increasing lists of 66 row and 66 column indices, and every entry (including zeros) must agree. Let $\operatorname{dist}_H(A)$ be the least number of binary cell edits to remove every copy, divided by $n^2$ for an $n\times n$ matrix $A$. For all reals $c,C>0$ there exist $n\ge1$, $0<\epsilon<1$ and $A$ with $\operatorname{dist}_H(A)\ge\epsilon$ and fewer than $c\epsilon^C n^{132}$ ordered copies of $H$.

## Depends on

- Ordered induced binary copies with separate increasing coordinate choices, explicit fixed pattern, and two-direction Hamming modification distance.

## Proof outline

Check the fixed block and bit orientations against the pattern in the comparator. Derive the witness for each exponent and constant from the construction's copy and edit counts, with normalization by n² and n¹³² respectively.

- Explicit sparse-copy/distance-gap construction for the anchored pattern, including the edit-distance lower bound and reparameterization for arbitrary powers.

## Sources

- [Comparator statement: `OAI.Problem348.no_polynomial_removal_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatrixRemoval.lean#L63-L72)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/190.md)
