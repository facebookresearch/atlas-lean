# Strict comparison of tracial ranks in the matrix stabilization

Use the matrix stabilization obtained from finite matrices over $A$ by the upper-left-corner inclusions (zero padding) and norm closure. In the unital comparison model use the C*-completion of the algebraic corner direct limit. In the projectionless comparison model use the closed union of the stage images in the quotient of bounded matrix families by norm-null families. At a fixed stage $k$, use the unnormalized sum of the diagonal trace values, not the averaged matrix trace.

In the unital model, for each tracial state $\tau$ and positive element $a$ in the corner completion, define its rank as the supremum over $j\ge0$ of the diagonal weight of $(a/\|a\|)^{1/(j+1)}$ (zero for the zero element), the weight being the supremum over the finite upper-left compressions of the extended nonnegative real conversion of their diagonal trace sum. Strict comparison asks that for every positive $a,b$ in the stabilization with $b\ne0$, if the rank of $a$ is strictly below that of $b$ for **every** tracial state, then $a$ is Cuntz subequivalent to $b$. This last relation is the approximation of $a$ in norm by elements $v^*bv$ in the stabilization. The universal trace test is vacuous if there are no tracial states, but the subequivalence conclusion is not.

In the nonunital model an extended trace is lower semicontinuous on the positive cone, takes values in $[0,\infty]$, sends zero to zero, is additive and nonnegative-homogeneous, and takes the same value on $x^*x$ and $xx^*$. It is densely finite if its finite domain is dense in the positive cone, and bounded if it is bounded on positive contractions. Given boundedness, extend its finite values to a bounded positive linear functional; for a nonzero trace, normalize it in norm, extend to the scalar unitization by $(z,a)\mapsto z+\tau_{\rm norm}(a)$, take the induced diagonal weight on the matrix stabilization of the unitization, and pull back along the stabilized inclusion. Rescale by the original functional norm, and let the zero trace extend by zero. Use the rank equal to the extended nonnegative liminf of the stabilized trace of the roots $a^{1/(j+1)}$. The precise comparison test for each positive $a,b$ with $b\ne0$ is: for each densely finite extended trace whose stabilized rank of $b$ is **one**, its stabilized rank of $a$ is **strictly below one**. This implies the same Cuntz subequivalence. Do not replace the finite-target-rank test by a comparison of arbitrary extended ranks.

## Sources

- [Definitions in `Model.lean`, lines 13–40](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L13-L40).
- [Definitions in `Model.lean`, lines 89–150](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L89-L150).
- [Definitions in `Model.lean`, lines 211–212](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L211-L212).
- [Definitions in `Model.lean`, lines 234–263](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L234-L263).
- [Definitions in `Model.lean`, lines 398–418](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L398-L418).
- [Definitions in `Model.lean`, lines 620–630](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L620-L630).
- [Definitions in `Model.lean`, lines 677–691](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L677-L691).
- [Definitions in `Model.lean`, lines 753–768](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L753-L768).
- [Definitions in `Model.lean`, lines 1204–1219](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1204-L1219).
- [Definitions in `Model.lean`, lines 1275–1276](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1275-L1276).
- [Definitions in `Model.lean`, lines 1304–1332](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1304-L1332).
- [Definitions in `Model.lean`, lines 1686–1691](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1686-L1691).
- [Definitions in `Model.lean`, lines 1830–1834](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1830-L1834).
- [Definitions in `Model.lean`, lines 1983–1999](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L1983-L1999).
- [Definitions in `Model.lean`, lines 2025–2031](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2025-L2031).
- [Definitions in `Model.lean`, lines 2074–2085](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2074-L2085).
- [Definitions in `Model.lean`, lines 2176–2184](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2176-L2184).
- [Definitions in `Model.lean`, lines 2201–2205](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2201-L2205).
- [Definitions in `Model.lean`, lines 2313–2325](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2313-L2325).
- [Definitions in `Model.lean`, lines 2373–2386](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2373-L2386).
- [Definitions in `Model.lean`, lines 2435–2447](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2435-L2447).
- [Definitions in `Model.lean`, lines 2451–2472](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2451-L2472).
- [Definitions in `Model.lean`, lines 2467–2472](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2467-L2472).
- [Definitions in `Model.lean`, lines 2513–2550](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2513-L2550).
- [Definitions in `Model.lean`, lines 2578–2593](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2578-L2593).
- [Definitions in `ChallengeDefinitions.lean`, lines 14–26](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/ChallengeDefinitions.lean#L14-L26).
- [Definitions in `Model.lean`, lines 13–18](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L13-L18).
- [Definitions in `Model.lean`, lines 981–982](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L981-L982).
- [Definitions in `OrthogonalElements.lean`, lines 287–295](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/OrthogonalElements.lean#L287-L295).
