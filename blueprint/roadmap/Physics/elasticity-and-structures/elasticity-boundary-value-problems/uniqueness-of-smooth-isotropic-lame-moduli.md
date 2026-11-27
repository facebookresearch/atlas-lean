# Global uniqueness of smooth isotropic Lamé moduli

Let $\Omega\subset\mathbb R^3$ be bounded, open and connected, with smooth boundary: near each boundary point there is an open partial homeomorphism of the ambient space with smooth coordinate map and inverse, sending the marked point to $y_1=0$ and flattening $\Omega$ to $y_1>0$ within its source. For $j=1,2$, let $\lambda_j,\mu_j$ be real functions smooth on open neighborhoods of $\overline\Omega$, with $\mu_j>0$ and $3\lambda_j+2\mu_j>0$ everywhere on $\overline\Omega$.

Represent $H^1(\Omega;\mathbb R^3)$ as the closure of globally smooth displacement jets $(u,\partial_1u,\partial_2u,\partial_3u)$ in the product of the four $L^2(\Omega;\mathbb R^3)$ spaces. The zero-trace subspace is the closure of the jets with compact support contained in $\Omega$. Boundary data are the **quotient** by that subspace, not an asserted identification with a chart-defined boundary Sobolev space. Use $\epsilon(u)_{ij}=(\partial_j u_i+\partial_i u_j)/2$ and

$$
a_{\lambda,\mu}(u,v)=\int_\Omega[\lambda\,\operatorname{div}u\operatorname{div}v+2\mu\,\textstyle\sum_{i,j}\epsilon(u)_{ij}\epsilon(v)_{ij}]\,dx.
$$

For datum $f$, the solution jet has trace $f$ and satisfies $a_{\lambda,\mu}(u,v)=0$ for every zero-trace test $v$. The source's totalized definition selects such a solution when one exists and a representative of $f$ otherwise. It defines $\Lambda_{\lambda,\mu}(f,g)=a_{\lambda,\mu}(u,v_g)$ using a representative $v_g$ of $g$. The physical interpretation requires existence of the variational solution and independence of the choice of $v_g$; neither is an extra hypothesis of the target.

If the two full pairings $\Lambda_{\lambda_j,\mu_j}$ agree for **all** pairs of quotient data, then $\lambda_1(x)=\lambda_2(x)$ and $\mu_1(x)=\mu_2(x)$ for every $x\in\Omega$. No reconstruction algorithm, partial-boundary measurement, or boundary-norm equivalence is asserted.

## Expansion

Show that the test jets define a closed linear subspace and prove the Korn and coercivity estimates needed for the Dirichlet solution. Establish representative-independence of the pairing via the weak equation. Derive the two-coefficient integral identity from equality of all pairings, and separate the source solution-construction and injectivity arguments that turn that identity into pointwise recovery.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ElasticityUniqueness.lean#L24-L104) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/372.md).
- OpenAI, [Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
