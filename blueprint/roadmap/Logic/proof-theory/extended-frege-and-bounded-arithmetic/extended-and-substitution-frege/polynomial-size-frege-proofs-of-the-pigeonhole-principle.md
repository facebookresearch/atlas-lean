# Polynomial-size Frege proofs of the pigeonhole principle

The propositional pigeonhole principle has Frege proofs of size polynomial in $n$ (Buss). Combined with Haken's exponential lower bound, this shows that Frege systems are exponentially more efficient than resolution.

For $n\ge 1$ let $p_{i,j}$, for $0\le i\le n$ and $0\le j<n$, be variables meaning that pigeon $i$ sits in hole $j$, and let

$$
\mathrm{PHP}_n \;=\; \bigwedge_{0\le i\le n}\ \bigvee_{0\le j<n} p_{i,j} \;\to\; \bigvee_{0\le i<m\le n}\ \bigvee_{0\le j<n} \left(p_{i,j}\wedge p_{m,j}\right),
$$

a formula of size proportional to $n^3$ stating that if each of $n+1$ pigeons sits in one of $n$ holes then some hole holds two pigeons.

**Theorem (Buss).** There is a constant $k$ such that for every $n$ the formula $\mathrm{PHP}_n$ has a Frege proof of size $O(n^k)$.

**Corollary.** $\mathrm{PHP}_n$ is a family of tautologies with polynomial-size Frege proofs whose resolution proofs require exponential size; hence Frege systems have an exponential speed-up over resolution (first shown by Urquhart with other formulas).

Earlier, Cook and Reckhow showed that $\mathrm{PHP}_n$ has extended Frege proofs of size $O(n^7)$.

## Expansion

The Cook–Reckhow extended Frege proof defines, by extension variables $q^k_{i,j}$, a sequence of maps $f_k:[k+1]\to[k]$ obtained from $f_{k+1}$ by redirecting the pigeon that lands in hole $k$, and proves that injectivity of $f_{k+1}$ implies injectivity of $f_k$, down to the impossible $f_1$; expanding the abbreviations naively blows up exponentially. Buss instead shows that Frege proofs can count: using carry-save addition, polynomial-size formulas compute the binary number of true formulas among $\varphi_1,\dots,\varphi_n$, and polynomial-size Frege proofs verify the basic properties of addition and comparison of these counts (Lemmas 1 to 6). The main proof, written as an extended Frege proof whose extension variables abbreviate counting formulas of controlled size, introduces variables $r^m_j$ for "hole $j$ is used by one of the first $m+1$ pigeons" and shows, assuming $\neg\mathrm{PHP}_n$, that the number of true $r^m_j$ is at least $m+1$ for every $m$, which is impossible for $m=n$ since there are only $n$ holes; Lemma 5(b) bounds the size of the expanded formulas, giving a genuine Frege proof (of size about $O(n^{20})$ by the author's estimate). The separation then uses [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md).

## Depends on

- [Frege proof systems](frege-system.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Extended Frege proof systems](extended-frege-system.md)
- [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- Samuel R. Buss, "Polynomial size proofs of the propositional pigeonhole principle", *Journal of Symbolic Logic* 52(4):916–927, 1987, doi:10.2307/2273826 (Section 3: the formula $\mathrm{PHP}_n$ and the Cook–Reckhow $eF$-proofs of size $O(n^7)$; Section 4: Lemmas 1 to 6 and Main Theorem 7; Section 5: Theorem 10, Frege versus resolution).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.9: Frege systems have polynomial-size proofs of the pigeonhole formulas, by counting with carry-save addition, while resolution needs exponential size).
