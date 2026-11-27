# R(lin) is superpolynomially stronger than R$^0$(lin)

R(lin) polynomially simulates Res($2$), with size measured in symbols, and so refutes the clique-coloring formulas with $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$ in polynomial size, while R$^0$(lin) needs size $n^{\Omega(\log n/\sqrt{\log\log n})}$; so R(lin) lacks feasible monotone interpolation.

**Res($2$) with symbol size.** A $2$-term is a conjunction of one or two literals and a $2$-DNF is a disjunction of $2$-terms. The size of a $2$-term is its number of literals, the size of a $2$-DNF is the total size of its $2$-terms, and the size of a Res($2$) proof is the total size of all its $2$-DNFs. A Res($2$) proof of $D$ from $2$-DNFs $K$ is a sequence of $2$-DNFs ending in $D$, each in $K$ or derived by *cut* (from $A\vee(l_1\wedge l_2)$ and $B\vee\neg l_1\vee\neg l_2$ derive $A\vee B$), *AND-introduction* (from $A\vee l_1$ and $B\vee l_2$ derive $A\vee B\vee(l_1\wedge l_2)$) or *weakening* (from $A$ derive $A\vee(l_1\wedge l_2)$), the $l_i$ being literals, not necessarily distinct. This is [Res($2$)](../k-dnf-resolution-and-random-cnf/k-dnf-resolution.md) with the total-symbol size measure, not the line count. A $2$-DNF $D$ translates into a disjunction $\widehat D$ of linear equations by writing each term $l_1\wedge l_2$ as $\widehat l_1+\widehat l_2=2$, with $\widehat{x_i}=x_i$ and $\widehat{\neg x_i}=1-x_i$ and the free terms moved to the right.

**Proposition.** [R(lin)](resolution-over-linear-equations.md) polynomially simulates Res($2$): if $\pi$ is a Res($2$) proof of a $2$-DNF $D$ from $2$-DNFs $K_1,\dots,K_t$, then there is an R(lin) proof of $\widehat D$ from $\widehat K_1,\dots,\widehat K_t$ of size polynomial in the size of $\pi$.

**Feasible monotone interpolation.** For disjoint variable vectors $\vec p$ ($n$ variables), $\vec q$, $\vec r$, let $A_1(\vec p,\vec q),\dots,A_k(\vec p,\vec q)$ and $B_1(\vec p,\vec r),\dots,B_\ell(\vec p,\vec r)$ be formulas with no common satisfying assignment, and let $\mathcal U_A$ and $\mathcal V_B$ be the sets of $u\in\{0,1\}^n$ that extend to a satisfying assignment of all $A_i$, respectively of all $B_j$. A refutation system $\mathcal P$ has the *feasible monotone interpolation property* if, whenever the $A_i$ stay satisfied when $\vec p$ is increased bitwise or the $B_j$ stay satisfied when $\vec p$ is decreased bitwise, every $\mathcal P$-refutation of size $S$ of $\bigwedge_iA_i\wedge\bigwedge_jB_j$ yields a monotone Boolean circuit of size polynomial in $S$ that outputs $1$ on $\mathcal U_A$ and $0$ on $\mathcal V_B$.

**Corollary.** Let $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$. Then the clique-coloring formulas $\mathrm{CLIQUE}^n_{k,k'}$ of [the R$^0$(lin) interpolation page](r0-lin-clique-coloring-lower-bound.md) have R(lin) refutations of size polynomial in $n$. Consequently R(lin) does not have the feasible monotone interpolation property, and R(lin) is superpolynomially stronger than [R$^0$(lin)](r0-lin-fragment.md): R(lin) polynomially simulates R$^0$(lin), but R$^0$(lin) does not polynomially simulate R(lin).

## Expansion

The Res($2$) rules become short R(lin) derivations, by induction on the number of lines as in the simulation of resolution; since R(lin) size counts symbols, the simulation is stated for the symbol size of the Res($2$) proof. Atserias, Bonet and Esteban gave polynomial-size Res($2$) refutations of $\mathrm{CLIQUE}^n_{k,k'}$ for these parameters, by reducing to the $k$ to $k'$ pigeonhole principle, which has short resolution refutations when $k$ is exponentially larger than $k'$ (Buss and Pitassi); the simulation carries them into R(lin). Comparing with the [R$^0$(lin) lower bound](r0-lin-clique-coloring-lower-bound.md) for the same parameters gives the separation. Feasible monotone interpolation would turn these refutations into small monotone circuits separating cliques from colourings, which the [Alon-Boppana bound](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md) rules out. This property differs from the non-monotone polynomial upper bounds on interpolant circuits that R$^0$(lin) has.

## Depends on

- [Resolution over linear equations R(lin)](resolution-over-linear-equations.md)
- [The fragment R0(lin)](r0-lin-fragment.md)
- [k-DNF resolution Res(k)](../k-dnf-resolution-and-random-cnf/k-dnf-resolution.md)
- [Interpolation and clique-coloring lower bounds for R0(lin)](r0-lin-clique-coloring-lower-bound.md)

## Proof depends on

None.

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 6.3, Definition 6.4 and the size of 2-DNFs, Proposition 2, Theorem 20 (cited), Corollaries 21 and 22; Section 8, Corollaries 30 and 31; Appendix A, Definition A.1).
