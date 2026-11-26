# Exact asymptotic moduli for measure-precompact Daugavet spaces

Let $E$ be a closed infinite-dimensional real subspace of $L^1(\mu)$ for a probability measure $\mu$. Suppose its entire unit ball has finite covers in the convergence-in-measure distance $d(f,g)=\inf\{a>0:\mu(|f-g|>a)<a\}$, at every strictly positive radius, with centers in $L^1(\mu)$. Assume $\|I+u\otimes\ell\|=1+\|u\otimes\ell\|$ for every rank-one operator $x\mapsto\ell(x)u$ on $E$.

For $\|x\|=1$ define $H(x,t)=\sup_F\inf_{y\in F,\|y\|\ge1}[(\|x+ty\|+\|x-ty\|)/2-1]$ and $D(x,t)=\sup_F\inf_{y\in F,\|y\|=1}[\|x+ty\|-1]$, with $F$ norm-closed and of finite codimension. For all $t>0$ these are respectively $\max(t/2,t-1)$ and $\max(0,t-2)$. The same formulas hold for their infima over unit $x$. For every equivalent real norm, defined by two positive comparison constants, its one-sided modulus is not positive at all $t>0$.

## Depends on

- The rank-one Daugavet equation, measure-distance covers and the cofinite moduli just defined.

## Proof depends on

- Upper and lower asymptotic cofinite estimates using both Daugavet slices and finite measure covers, and the obstruction under an arbitrary equivalent norm.

## Expansion

Separate the two estimates for each pointwise formula, take infima only after the local equalities, and then prove the isomorphic non-AUC property; it is not a consequence of vanishing for one norm alone.

## Sources

- OpenAI, [DaugavetModuli comparator, exact_main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DaugavetModuli.lean#L72-L84).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
