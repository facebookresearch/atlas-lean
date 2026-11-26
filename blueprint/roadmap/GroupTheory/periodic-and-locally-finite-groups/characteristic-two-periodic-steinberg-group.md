# An infinite finitely presented periodic Steinberg group

There exists a unital ring $R$ with an $\mathbb F_2$-algebra structure such that $\operatorname{St}_{12}(R)$ is infinite and finitely presented, and every element has finite order. Here the group has generators $x_{ij}(a)$ for $i\ne j$ in twelve indices and $a\in R$, with relations $x_{ij}(a+b)=x_{ij}(a)x_{ij}(b)$, $[x_{ij}(a),x_{kl}(b)]=1$ for $j\ne k$ and $i\ne l$, and $[x_{ij}(a),x_{jk}(b)]=x_{ik}(ab)$ for pairwise distinct $i,j,k$. Use $[x,y]=xyx^{-1}y^{-1}$. Periodicity is $\forall g\,\exists m>0\ (g^m=1)$, not a common exponent or residual finiteness.

## Depends on

- The indicated Steinberg presentation and group periodicity.

## Proof depends on

- Existence of the coefficient ring with the necessary nil properties, and finiteness, infinitude and periodicity arguments for its Steinberg group.

## Expansion

Establish the source ring construction and separate finite presentation of the group from the potentially infinite generator family of the displayed presentation. Prove periodicity for arbitrary words.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PeriodicGroup.lean#L51-L53) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PeriodicGroup.lean).
