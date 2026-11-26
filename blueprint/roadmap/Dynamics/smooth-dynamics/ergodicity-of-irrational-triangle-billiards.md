# Ergodicity of the specular billiard flow in an irrational triangle

Let $Q\subset\mathbb C$ be the open interior of the convex hull of three affinely independent vertices $v_i$, numbered cyclically modulo $3$. Suppose at least one angle between $v_{i+1}-v_i$ and $v_{i+2}-v_i$, divided by $\pi$, is irrational. On the ambient phase space $\mathbb C\times S^1$, let $\mu$ be normalized area restricted to $Q$ times the pushforward of $d\theta/(2\pi)$ on $[0,2\pi)$ by $\theta\mapsto e^{i\theta}$.

A regular chain has bilateral collision times $t_n$ strictly increasing and unbounded at each end, with $t_0<0<t_1$. At each index $n$ it records a collision point $p_n$, the side index $j_n\in\{0,1,2\}$ whose open segment from $v_{j_n}$ to $v_{j_n+1}$ contains $p_n$, and an outgoing unit direction $d_n\in S^1$. The tangent is the derived vector $e_n=v_{j_n+1}-v_{j_n}$, not extra data. On $[t_n,t_{n+1})$ the state is $(p_n+(t-t_n)d_n,d_n)$; the open flight stays in $Q$ and joins the two collision points. At each collision $d_n=(e_n/\overline{e_n})\overline{d_{n-1}}$. The initial point and direction equal this state at time $0$. At a singular input with no such chain, use the input as the state at all times.

The claim is that $\mu$ is a probability, almost every input has a regular chain, and any two chains for the same input are equal, even without an almost-everywhere qualification on uniqueness. Each resulting map $B_t$ preserves $\mu$; for each pair $s,t\in\mathbb R$, $B_{s+t}=B_s\circ B_t$ modulo a $\mu$-null set. Every measurable $A$ invariant modulo null sets under all $B_t$ has measure $0$ or $1$. This is **ergodicity** of the flow, not weak mixing and not a statement about the collision map alone.

## Expansion

Prove the first-collision and unique continuation lemmas in the open sides, exclude vertex hits and finite-time accumulations on a conull set, and prove measure preservation and the flow law for the fixed-time ambient maps. Then isolate the irrational-angle ergodicity argument; it must apply to each qualifying triangle without parameter genericity.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IrrationalTriangleBilliard.lean#L19-L121) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/150.md).
- OpenAI, [Ergodicity of triangular billiards with an irrational angle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026.pdf) (September 25, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
