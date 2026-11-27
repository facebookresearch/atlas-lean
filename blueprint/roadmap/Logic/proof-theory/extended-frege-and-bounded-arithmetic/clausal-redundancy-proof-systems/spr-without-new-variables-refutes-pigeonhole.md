# SPR refutations of pigeonhole principles without new variables

Subset propagation redundancy needs neither new variables nor deletion to refute the pigeonhole principle and the bit pigeonhole principle in polynomial size, although these formulas are hard for bounded-depth Frege.

For $n\ge 1$ and $[n]=\{0,\dots,n-1\}$, $\mathrm{PHP}_n$ consists of the pigeon axioms $\bigvee_{j\in[n]}p_{i,j}$ for each $i\in[n+1]$ and the hole axioms $\bar p_{i,j}\vee\bar p_{i',j}$ for all $i<i'$ in $[n+1]$ and $j\in[n]$.

For $n=2^k$, the bit pigeonhole principle $\mathrm{BPHP}_n$ gives each pigeon $x$ with $0\le x<n+1$ variables $p^x_1,\dots,p^x_k$ for the bits of its hole $y\in\{0,1\}^k$. Writing $(x\not\to y)$ for the clause $\bigvee_i (p^x_i\ne y_i)$, its axioms are

$$
(x\not\to y)\vee(x'\not\to y)\qquad\text{for all holes } y \text{ and all distinct pigeons } x,x'.
$$

**Theorem.** (a) (Heule, Kiesl and Biere) $\mathrm{PHP}_n$ has polynomial-size SPR$^-$ refutations. (b) (Buss–Thapen) $\mathrm{BPHP}_n$ has polynomial-size SPR$^-$ refutations.

The source also gives polynomial-size SPR$^-$ refutations of the parity principle, the clique-colouring principle and the Tseitin formulas.

## Expansion

The proofs exploit symmetries. If the pairs $(\alpha_i,\tau_i)$ satisfy $\Gamma|_{\alpha_i}=\Gamma|_{\tau_i}$, each $\alpha_i$ and $\tau_i$ are contradictory with the same domain, and earlier $\alpha_j$ are disjoint from or contradict $\tau_i$, then SPR steps add all clauses $\overline{\alpha_i}$ (Lemma 4.2). For $\mathrm{PHP}_n$ the pairs come from swapping two holes; the added clauses resolve with hole axioms to unit clauses $\bar p_{j,i}$ for $j>i$, which remove pigeon $i$ and hole $i$ and reduce the instance to a renamed $\mathrm{PHP}_{n-1}$; iterating refutes the formula. For $\mathrm{BPHP}_n$ the same strategy introduces the clauses $C_{m,x,y}=(m\not\to y)\vee(x\not\to m)$ for $m<n-1$ and $x,y>m$, after which a polynomial-size resolution refutation exists (Lemma 4.5). By contrast, bounded-depth Frege refutations of $\mathrm{PHP}_n$ require exponential size.

## Depends on

- [DRAT, PR and related clausal proof systems](drat-and-pr-proof-systems.md)

## Proof depends on

- [Blocked, RAT, propagation-redundant and substitution-redundant clauses](propagation-and-substitution-redundancy.md)

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Section 4: Definition 4.1 and Lemma 4.2; Section 4.1: $\mathrm{PHP}_n$ and Theorem 4.3; Section 4.2: $\mathrm{BPHP}_n$, Theorem 4.4 and Lemma 4.5; Theorems 4.6, 4.7 and 4.10 for parity, clique-colouring and Tseitin formulas).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: SPR without new variables or deletion gives polynomial-size proofs of pigeonhole, clique-colouring and Tseitin formulas, which are hard for bounded-depth Frege).
