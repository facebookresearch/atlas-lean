# Subcritical Hénon–Lane–Emden nonexistence off the origin

Let $n\ge2$, let $p,q>0$ and let $A,B$ be arbitrary reals such that $(n+A)/(p+1)+(n+B)/(q+1)>n-2$. There are no everywhere positive real functions $u,v$ on $\mathbb R^n$ that are continuous on all of $\mathbb R^n$, are $C^2$ off the origin and satisfy at every $x\ne0$

$$-\Delta u(x)=\|x\|^A v(x)^p,\qquad -\Delta v(x)=\|x\|^B u(x)^q.$$

All scalar powers are real powers of positive quantities at the points where the equations hold. No equation or differentiability is required at zero; the critical equality is not included.

## Depends on

- The Euclidean Laplacian, real powers on positive inputs, and punctured-space regularity.

## Proof depends on

- A priori estimates handling both the puncture and infinity, and the subcritical integral-identity contradiction for the weighted system.

## Expansion

Separate origin boundary terms under continuity-only hypotheses from the estimates at infinity. Keep the stated weights and strict inequality through the contradiction; an unweighted proof or a superlinear-only argument does not close the target.

## Sources

- OpenAI, [HenonEmden comparator, main_nonexistence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HenonEmden.lean#L24-L28).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/370.md).
