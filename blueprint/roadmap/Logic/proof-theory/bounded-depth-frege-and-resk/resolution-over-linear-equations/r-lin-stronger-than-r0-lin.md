# R(lin) is superpolynomially stronger than R$^0$(lin)

R(lin) polynomially simulates Res($2$) and therefore refutes the clique-coloring formulas with $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$ in polynomial size, while R$^0$(lin) needs size $n^{\Omega(\log n/\sqrt{\log\log n})}$; so R(lin) lacks feasible monotone interpolation.

**Proposition.** [R(lin)](resolution-over-linear-equations.md) polynomially simulates [Res($2$)](../k-dnf-resolution-and-random-cnf/k-dnf-resolution.md): if $\pi$ is a Res($2$) proof of a $2$-DNF $D$ from $2$-DNFs $K_1,\dots,K_t$, then there is an R(lin) proof of the translation $\widehat D$ from $\widehat K_1,\dots,\widehat K_t$ of size polynomial in the size of $\pi$.

**Corollary.** Let $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$. Then the clique-coloring formulas $\mathrm{CLIQUE}^n_{k,k'}$ have R(lin) refutations of size polynomial in $n$. Consequently R(lin) does not have the feasible monotone interpolation property, and R(lin) is superpolynomially stronger than [R$^0$(lin)](r0-lin-fragment.md): R(lin) polynomially simulates R$^0$(lin), but R$^0$(lin) does not polynomially simulate R(lin).

## Expansion

Each $2$-DNF is translated into a disjunction of linear equations by writing a term $l_1\wedge l_2$ as $\widehat l_1+\widehat l_2=2$, where $\widehat{x_i}=x_i$ and $\widehat{\neg x_i}=1-x_i$, so the Res($2$) rules become short R(lin) derivations. Atserias, Bonet and Esteban gave polynomial-size Res($2$) refutations of $\mathrm{CLIQUE}^n_{k,k'}$ for these parameters, by reducing to the $k$ to $k'$ pigeonhole principle, which has short resolution refutations when $k$ is exponentially larger than $k'$ (Buss and Pitassi); the simulation carries them into R(lin). Comparing with the [R$^0$(lin) lower bound](r0-lin-clique-coloring-lower-bound.md) for the same parameters gives the separation. Feasible monotone interpolation would turn these refutations into small monotone circuits separating cliques from colourings, which the [Alon-Boppana bound](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md) rules out.

## Depends on

- [Resolution over linear equations R(lin)](resolution-over-linear-equations.md)
- [The fragment R0(lin)](r0-lin-fragment.md)
- [k-DNF resolution Res(k)](../k-dnf-resolution-and-random-cnf/k-dnf-resolution.md)

## Proof depends on

- [Interpolation and clique-coloring lower bounds for R0(lin)](r0-lin-clique-coloring-lower-bound.md)

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 6.3, Definition 6.4, Proposition 2, Theorem 20 (cited), Corollaries 21 and 22; Section 8, Corollaries 30 and 31).
