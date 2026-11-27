# Tightness of the flattening for tree-like proofs

For every depth $d$ there are balanced formulas of depth $d+2$ with tree-like Frege proofs of size $s_n$ such that every tree-like depth-$d$ Frege proof needs size $2^{s_n^{\Omega(1/d)}}$, so the Frege-to-bounded-depth flattening cannot be improved for tree-like proofs.

**Theorem.** For every $d$ there is a sequence of balanced formulas $\varphi_n$ of depth $d+2$ that are provable in Frege by tree-like proofs of size $s_n$, such that every tree-like $\mathrm{AC}^0_d$-Frege proof of $\varphi_n$ requires size

$$
2^{s_n^{\Omega(1/d)}}.
$$

Since the $\varphi_n$ are balanced, the [flattening theorem](frege-proofs-flatten-to-bounded-depth.md) applies to them with $k=d-2$ and gives tree-like $\mathrm{AC}^0_d$-Frege proofs essentially matching this lower bound.

## Expansion

Take $\varphi_n$ to be the pigeonhole principle $\mathrm{PHP}_n$ ($n+1$ pigeons, $n$ holes) with each variable replaced by a Sipser function of depth $d$. Buss's polynomial-size Frege proofs of $\mathrm{PHP}_n$ can be made tree-like by squaring their size, and substituting the Sipser functions gives tree-like Frege proofs of size $n^{d+O(1)}$. Krajíček's lower bound of $2^{n^{\Omega(1)}}$ for tree-like $\mathrm{AC}^0_d$ proofs of these formulas gives the other direction. The source conjectures that the simulation is also tight for CNF formulas and dag-like proofs; for the pigeonhole principle itself the known depth-$d$ lower bounds have exponents that decay much faster in $d$, an artifact of the switching-lemma technique. The analogous circuit statement is that polynomial-size formulas have depth-$d$ circuits of size $\exp(n^{O(1/d)})$, which is tight by the [depth-$d$ size bound for parity](../../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/depth-d-circuit-size-of-parity.md).

## Depends on

- [Bounded-depth Frege proofs](bounded-depth-frege-proofs.md)

## Proof depends on

- [Frege proofs flatten to subexponential bounded-depth Frege proofs](frege-proofs-flatten-to-bounded-depth.md)

## Sources

- Yuval Filmus, Toniann Pitassi and Rahul Santhanam, "Exponential Lower Bounds for AC0-Frege Imply Superpolynomial Frege Lower Bounds", *Automata, Languages and Programming (ICALP 2011), Part I*, Lecture Notes in Computer Science 6755, pp. 618-629, 2011, https://doi.org/10.1007/978-3-642-22006-7_52 (Section 5.1, Theorem 3).
