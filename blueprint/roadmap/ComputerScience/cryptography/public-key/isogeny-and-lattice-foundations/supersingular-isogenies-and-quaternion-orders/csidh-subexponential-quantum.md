# Quantum subexponential attacks on commutative isogeny group actions

For any free and transitive action of an abelian group $G$ on a set $X$ whose action is efficiently computable (in particular the CSIDH action), recovering $[\mathfrak{a}]$ from $(E,[\mathfrak{a}]\star E)$ reduces to an abelian hidden shift problem, which Kuperberg's algorithm solves in quantum time $2^{O(\sqrt{\log|G|})}$ (subexponential), using that many group-action evaluations. Consequently CSIDH parameters must account for subexponential quantum attacks, unlike lattice or hash-based schemes where only polynomial (Grover-type) quantum speedups are known.

## Proof sketch

Define $f_0(g)=g\star E$ and $f_1(g)=g\star E'$; then $f_1(g)=f_0(g[\mathfrak{a}])$, a hidden shift by $[\mathfrak{a}]$. Kuperberg's sieve combines coset states to learn the shift bit by bit in subexponential time and queries, each query being a superposition of group-action evaluations.

## Depends on

- [The CSIDH class group action on F_p-rational supersingular curves](csidh-group-action.md)

## Proof depends on

- [BQP](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Andrew Childs, David Jao, Vladimir Soukharev, "Constructing Elliptic Curve Isogenies in Quantum Subexponential Time", Journal of Mathematical Cryptology (2014).
- Greg Kuperberg, "A Subexponential-Time Quantum Algorithm for the Dihedral Hidden Subgroup Problem", SIAM Journal on Computing (2005).
- Wouter Castryck, Tanja Lange, Chloe Martindale, Lorenz Panny, Joost Renes, "CSIDH: An Efficient Post-Quantum Commutative Group Action", ASIACRYPT (2018), IACR ePrint 2018/383.
