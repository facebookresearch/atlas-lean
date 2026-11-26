# A nonflat one-homogeneous Bernoulli minimizer in dimension seven

There is a real function $u$ on $\mathbb R^7$ with an $H^1_{\rm loc}$ weak gradient, nonnegative and not identically zero almost everywhere, such that for every $\lambda>0$, $u(\lambda x)=\lambda u(x)$ for almost every $x$. On every open ball of positive radius, $u$ minimizes

$$\int_B\big(\|\nabla u\|^2+\mathbf 1_{\{u>0\}}\big)$$

among nonnegative almost-everywhere $H^1(B)$ competitors $v$ with $v-u\in H^1_0(B)$. Here a weak gradient satisfies integration by parts against every compactly supported smooth test in every constant direction; $H^1$ requires both the function and gradient in $L^2$, and $H^1_0$ uses simultaneous $L^2$ approximation of the function and gradient by compactly supported smooth functions and their gradients. There is no unit vector $e$ with $u(x)=\max(\langle x,e\rangle,0)$ almost everywhere.

## Depends on

- Ballwise Sobolev and zero-trace models and the full volume-one comparison functional above.

## Proof depends on

- Construction of the dimension-seven homogeneous cone and its global minimality against all ballwise Sobolev competitors.

## Expansion

Separate the profile construction and its Sobolev regularity from the energy comparison and the nonflatness test. Neither minimality against smooth competitors alone nor the classification of lower-dimensional cones is the assertion.

## Sources

- OpenAI, [BernoulliNonflatInSeven comparator, nonflat_in_seven](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BernoulliNonflatInSeven.lean#L78-L81).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/367.md).
