# A CH obstruction at the countable Hanf threshold

Assume $2^{\aleph_0}=\aleph_1$. There is an abstract elementary class in a countable relational language (countably many relation symbols in total, each of finite arity) with Löwenheim–Skolem number exactly $\aleph_0$. At $\beth_{\omega_2}=\beth_{\operatorname{ord}((2^{\aleph_0})^+)}$ it has two nonisomorphic models, and at every cardinal $\mu\ge\beth_{\operatorname{ord}((2^{\aleph_1})^+)}$ it has a model and any two models of size $\mu$ are isomorphic.

The class consists of set-coded relational structures with an isomorphism-invariant coherent strong-substructure partial order refining substructure, closed under unions of nonempty ordinal chains strongly in every common strong upper bound. A Löwenheim–Skolem bound $\theta$ is at least $\aleph_0$ and the language size and yields strong submodels containing any specified subset $A$ of size at most $|A|+\theta$. No amalgamation or tameness is assumed.

## Depends on

- AEC axioms and cardinal arithmetic, including ordinal-indexed beth and exact Löwenheim–Skolem number.

## Proof depends on

- Construction of the relational class, two models at the endpoint and a separate uniqueness-and-existence argument throughout the tail.

## Expansion

Verify coherence and chain unions for the actual relational construction. Compute the endpoint using CH and distinguish the two endpoints; do not replace this by failure of eventual categoricity.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CHObstruction.lean#L96-L102) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CHObstruction.lean).
