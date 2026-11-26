# Krajíček's interpolation theorem for semantic derivations

Let the variables be split into shared $X$ ($|X| = n$) and private $Y$, $Z$; let $\mathcal{A}$ be initial sets depending only on $X \cup Y$ and $\mathcal{B}$ initial sets depending only on $X \cup Z$. Suppose there is a semantic refutation from $\mathcal{A} \cup \mathcal{B}$ with $k$ lines, each of which, viewed as a function of the $(X \cup Y)$-part and the $Z$-part, has two-party communication complexity at most $t$. Then there is a Boolean circuit of size $(k + 2n) \cdot 2^{O(t)}$ (and in fact of size $(k\, 2^{2t} + 1)\, 2^{2t+1}$, independent of $n$) separating $\{u : \exists q\; (u,q) \models \mathcal{A}\}$ from $\{v : \exists r\; (v,r) \models \mathcal{B}\}$; if the communication is monotone, the circuit can be taken monotone.

## Proof sketch

Alice holds a model of $\mathcal{A}$ and Bob a model of $\mathcal{B}$; they walk backwards from the empty line along lines falsified by the mixed assignment, which cannot end at a derived line or a $\mathcal{B}$-set, so it ends at an $\mathcal{A}$-set where a coordinate of $X$ on which their shared parts differ is found. This is a dag-like protocol for the Karchmer–Wigderson game, and such protocols convert into circuits.

## Depends on

- [Semantic derivations](semantic-derivations.md)
- [Communication cost of a protocol](../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/depth.md)
- [Boolean gates](../../../TheoryOfComputation/circuit-complexity/boolean-circuits/boolean-gate.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997.
