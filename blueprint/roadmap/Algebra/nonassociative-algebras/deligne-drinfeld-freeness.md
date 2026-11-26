# Deligne–Drinfeld freeness and weight completion

Work over $\mathbb Q$. Let $L$ be the free Lie algebra on $x,y$, both of weight one. Write $p(a,b)$ for substitution into a Lie polynomial. In the four-strand Lie algebra take $t_{ij}=t_{ji}$ for $0\le i<j\le3$, impose $[t_{ij},t_{kl}]=0$ for four distinct indices and $[t_{ij},t_{ik}+t_{jk}]=0$ for three distinct indices. Let $W\subset L$ be the simultaneous solution space of

$$p(x,y)+p(y,x)=0,\quad p(x,y)+p(y,-x-y)+p(-x-y,x)=0,$$

$$p(t_{01},t_{12}+t_{13})+p(t_{02}+t_{12},t_{23})
=p(t_{12},t_{23})+p(t_{01}+t_{02},t_{13}+t_{23})+p(t_{01},t_{12}).$$

Let $D_p$ be the derivation with $D_p x=0$, $D_p y=[y,p]$, and put $\{p,q\}=D_pq-D_qp+[p,q]$. There is a rational linear equivalence $e$ from the free Lie algebra with generators of weights $2k+3$ ($k\ge0$) to $W$. For each $n$, $e(a)$ is in ordinary weight $n$ exactly when $a$ is in weight $n$; moreover $e([a,b])=\{e(a),e(b)\}$. Equip both ambient free Lie algebras with the discrete topology, their weight spaces with the induced discrete topologies, and the completions with the product topologies. The componentwise maps on completions are continuous and inverse. For homogeneous sequences $(a_i),(b_i)$ in the completed odd-weight free Lie algebra and each $n$, the equality in $L$ is

$$
e\!\left(\sum_{i=0}^n[a_i,b_{n-i}]\right)=\sum_{i=0}^n\{e(a_i),e(b_{n-i})\}.
$$

The terms on the right are the components of the two actual images under the completed map.

## Depends on

- Four-strand Lie algebra, substitution, weight spaces and the Ihara derivation on the free Lie algebra.

## Proof depends on

- Homogeneous freeness and generation for the simultaneous solution space; continuity and bracket transport on its product completion.

## Expansion

Construct the braid quotient and the Ihara operation from free Lie algebra lifts. Decompose the pentagon by weight, isolate the odd-weight generators and prove injectivity and surjectivity of the graded map before extending componentwise.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DeligneDrinfeld.lean#L189-L191) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DeligneDrinfeld.lean).
