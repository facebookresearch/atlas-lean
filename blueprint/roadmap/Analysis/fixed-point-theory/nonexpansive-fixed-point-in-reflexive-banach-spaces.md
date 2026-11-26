# Fixed points of nonexpansive maps in real reflexive Banach spaces

Let $X$ be a real Banach space with surjective canonical map into its continuous bidual, sending $x$ to evaluation at $x$. If $C\subset X$ is nonempty, norm-closed, bounded and convex and $F:C\to C$ satisfies $\|F(a)-F(b)\|\le\|a-b\|$ in the original norm for every $a,b\in C$, then some $a\in C$ satisfies $F(a)=a$. The statement requires neither normal structure nor uniform convexity, separability, or weak continuity of $F$.

## Depends on

- [Nonexpansive self-map](browder-g-hde-kirk-fixed-point-theorem/is-nonexpansive-self-map.md).

## Proof depends on

- Passage from canonical reflexivity to weak compactness of the constraint set, and an actual fixed-point argument using no normal-structure premise.

## Expansion

Align canonical bidual evaluation with the existing reflexivity model. Isolate the weak-compactness argument and the step upgrading approximate fixed points to a member fixed by $F$ in the original norm. The Browder–Göhde–Kirk result with normal structure does not establish this endpoint.

## Sources

- OpenAI, [ReflexiveFixedPoints comparator, exists_fixedPoint_of_canonicallyReflexive](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ReflexiveFixedPoints.lean#L19-L30).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/328.md).
