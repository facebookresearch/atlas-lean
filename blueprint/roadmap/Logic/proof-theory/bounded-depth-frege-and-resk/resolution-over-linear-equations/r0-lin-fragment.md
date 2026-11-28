# The fragment R$^0$(lin)

R$^0$(lin) restricts R(lin) to lines with constant integer coefficients that split into a constant number of blocks, each either a disjunction of equations differing only in their free terms or a translated clause.

A disjunction $D$ of linear equations whose variables have constant integer coefficients (free terms are unbounded) is an *R$^0$(lin)-line* if it can be partitioned into a constant number $k$ of sub-disjunctions $D_1,\dots,D_k$, each of which either consists of an unbounded disjunction of linear equations that differ only in their free terms or is the translation of a clause. Merging clause parts, every R$^0$(lin)-line has the form

$$
\bigvee_{i\in I_1}\bigl(\vec a^{(1)}\cdot\vec x=\ell^{(1)}_i\bigr)\vee\dots\vee\bigvee_{i\in I_k}\bigl(\vec a^{(k)}\cdot\vec x=\ell^{(k)}_i\bigr)\vee\bigvee_{j\in J}(x_j=b_j),
$$

with $k$ and all coefficients $a^{(t)}_r$ integer constants, $b_j\in\{0,1\}$, and unbounded index sets $I_1,\dots,I_k,J$. The proof system *R$^0$(lin)* is the restriction of [R(lin)](resolution-over-linear-equations.md) in which every proof line is an R$^0$(lin)-line.

## Expansion

An example is $(x_1+\dots+x_\ell=1)\vee\dots\vee(x_1+\dots+x_\ell=\ell)\vee(x_{\ell+1}=1)\vee\dots\vee(x_n=1)$. Every line in the simulation of resolution is a translated clause, so R$^0$(lin) is complete, and it is even implicationally complete. It resembles a system working with a constant number of linear inequalities with constant coefficients but can express parity. R(lin) polynomially simulates R$^0$(lin), and the converse fails: R$^0$(lin) has [polynomial upper bounds on interpolants and exponential clique-coloring lower bounds](r0-lin-clique-coloring-lower-bound.md), while [R(lin) refutes the clique-coloring formulas in polynomial size](r-lin-stronger-than-r0-lin.md).

## Depends on

- [Resolution over linear equations R(lin)](resolution-over-linear-equations.md)

## Proof depends on

None.

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 3.3, Definitions 3.2 and 3.3, Corollary 12).
