# Frege proofs flatten to subexponential bounded-depth Frege proofs

Every Frege proof of size $s$ of a formula of logical depth $O(\log s)$ can be converted, for each $k\ge1$, into a depth-$(k+2)$ Frege proof of size $2^{O(k s^{O(1/k)})}$. So purely exponential lower bounds for bounded-depth Frege would give superpolynomial Frege lower bounds.

**Theorem.** Let $\varphi$ be a formula provable in Frege (the sequent calculus PK) in size $s$, with logical depth $\mathrm{ldp}(\varphi)\le C\log s$. For every $k\ge1$ there is an $\mathrm{AC}^0_{k+2}$-Frege proof of $\varphi$ of size

$$
2^{O(k s^{O(C/k)})}.
$$

If the original proof is tree-like, so is the new one.

**Corollary.** Let $\varphi$ be a formula of size $s$ and logical depth at most $C\log s$. If $\varphi$ has a Frege proof of size $O(s^c)$, then for every $k\ge1$ it has an $\mathrm{AC}^0_{k+2}$-Frege proof of size $2^{O(cks^{O(C/k)})}$.

In particular, a proof size lower bound of $2^{n^{\omega(1/d)}}$ for CNF tautologies in depth-$d$ Frege would yield a superpolynomial size lower bound for Frege.

## Expansion

By Reckhow's balancing theorem a size-$s$ PK proof can be made polynomial size with every formula of logical depth $O(\log s)$. A balanced formula is cut at the levels of a depth vector $\mathbf d=(d_1,\dots,d_k)$; the top piece is written as a CNF and the pieces below alternately as DNFs and CNFs, giving the conjunctive and disjunctive flattened forms $C(\varphi;\mathbf d)$ and $D(\varphi;\mathbf d)$. If the largest gap between consecutive levels (the extent) is $x$, these forms have depth at most $k+2$ and size $2^{O(k2^x)}$. The technical core is a family of tree-like proofs, cutting only on formulas of depth about $k+3$, that flattened forms for different depth vectors are equivalent and commute with the connectives. Replacing every formula of the balanced proof by its flattened form with equally spaced levels then gives a proof of size $s\,2^{O(k2^{D/k})}$ for maximum logical depth $D$, and $D=C\log s$ gives the bound. The same simulation shows the bound is [tight for tree-like proofs](tree-like-flattening-is-tight.md), and gives a short derivation of the result that bounded-depth Frege is not weakly automatizable under a Diffie-Hellman hardness assumption (compare [cryptographic non-automatability of Frege-type systems](../../automatability-of-proof-systems/bpr-frege-non-automatable.md)). Superpolynomial Frege lower bounds remain [open](../../superpolynomial-lower-bounds-for-frege-proofs.md).

## Depends on

- [Bounded-depth Frege proofs](bounded-depth-frege-proofs.md)

## Proof depends on

None.

## Sources

- Yuval Filmus, Toniann Pitassi and Rahul Santhanam, "Exponential Lower Bounds for AC0-Frege Imply Superpolynomial Frege Lower Bounds", *Automata, Languages and Programming (ICALP 2011), Part I*, Lecture Notes in Computer Science 6755, pp. 618-629, 2011, https://doi.org/10.1007/978-3-642-22006-7_52 (Theorem 1 (Reckhow), Definitions 4 and 5, Lemmas 1 and 15, Theorem 2, Corollary 1, Section 5.2).
