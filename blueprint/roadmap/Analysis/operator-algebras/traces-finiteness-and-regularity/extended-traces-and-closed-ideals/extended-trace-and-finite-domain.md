# Extended traces and their finite square-trace domains

Let $A$ be a possibly nonunital complex C*-algebra with the star order and its norm topology. An extended trace is a function $\tau:A_+\to[0,+\infty]$ on the positive cone, lower semicontinuous for the induced topology. It sends zero to zero, is additive on $A_+$ and is homogeneous for strictly positive real scalars: $\tau(ra)=r\tau(a)$ for $r>0$. The tracial condition is $\tau(x^*x)=\tau(xx^*)$ for every $x\in A$. No density or finiteness of its finite-valued cone is assumed. Addition of traces is pointwise.

The finite square-trace domain and its norm closure are

$$D_\tau=\{x\in A:\tau(x^*x)<+\infty\},\qquad I_\tau=\overline{D_\tau}^{\|\cdot\|}.$$

The closure in this formula is a closure of sets. The additive, star-algebra and two-sided ideal properties of the domain or its closure are separate assertions. In the comparator, the closed star subalgebra is obtained by first equipping $D_\tau$ with the nonunital star-subalgebra structure and then taking its topological closure.

## Depends on

- [C*-algebra](../../cstar-algebra.md).

## Sources

- OpenAI, [positive cone and extended trace](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L13-L42), [finite square-trace domain and its closure](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L69-L95).
