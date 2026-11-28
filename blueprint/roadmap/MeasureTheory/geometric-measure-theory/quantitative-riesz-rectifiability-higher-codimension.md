# Quantitative higher-codimension rectifiability from Riesz transforms

Fix integers $d\geq4$, $2\leq n\leq d-2$, a real $C_{\rm AD}\geq1$, and a nonnegative $C_R$. There exist $\theta>0$ and $M\geq0$, depending only on these parameters, with the following property. Take any regular measure $\mu$ on Euclidean $\mathbb R^d$ with $r^n/C_{\rm AD}\leq\mu(B(x,r))\leq C_{\rm AD}r^n$ for all $x\in\operatorname{supp}\mu$ and $0<r\leq\operatorname{diam}(\operatorname{supp}\mu)$ (allowing infinite diameter). Suppose for every $\epsilon>0$, the hard truncation $T_\epsilon f(x)=\int_{|x-y|>\epsilon} f(y)(x-y)/|x-y|^{n+1}\,d\mu(y)$ sends real $L^2(\mu)$ into vector-valued $L^2(\mu)$ with norm at most $C_R$. For every such $x,r$ some $M$-Lipschitz $g:B_{\mathbb R^n}(0,r)\to\mathbb R^d$ has $\mu(B(x,r)\cap g(B(0,r)))\geq\theta r^n$. All balls used here are open.

## Depends on

Topological support and its extended diameter, uniform AD regularity for admissible radii, and the vector-valued hard-truncation operator on actual measurable functions.

## Proof depends on

Quantitative geometric control from the Riesz bound and conversion to big pieces of Lipschitz images with constants uniform over the class of measures.

## Expansion

Expose the scale-localized geometric estimate and its dependence on $d,n,C_{\rm AD},C_R$ before constructing the image in each ball. Account separately for unbounded supports and do not substitute a claim about principal values or mere rectifiability.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RieszQuantitative.lean#L56-L59) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/081.md).
