# Resolution over linear equations R(lin)

R(lin) is the refutation system whose lines are disjunctions of integer linear equations over Boolean variables; it resolves two lines by adding or subtracting one equation from each, and with weakening, simplification of $0=k$ for $k\ne0$, and Boolean axioms it is a sound and complete Cook-Reckhow system extending resolution.

A *linear equation* is $a_1x_1+\dots+a_nx_n=a_0$ with integer coefficients; $a_0$ is its *free term*. A *disjunction of linear equations* $\bigvee_{j=1}^t(\vec a^{(j)}\cdot\vec x=a^{(j)}_0)$, $t\ge0$, is satisfied by a $0/1$ assignment when some equation holds; the empty disjunction is false. The size of an equation is $\sum_{i=0}^n|a_i|$, i.e. coefficients are written in *unary*, and the size of a disjunction is the total size of its equations. A clause $\bigvee_{i\in I}x_i\vee\bigvee_{j\in J}\neg x_j$ is translated as $\bigvee_{i\in I}(x_i=1)\vee\bigvee_{j\in J}(x_j=0)$.

Let $K$ be a collection of disjunctions of linear equations. An *R(lin) proof* of $D$ from $K$ is a sequence $D_1,\dots,D_\ell=D$ in which each $D_i$ is in $K$, is a *Boolean axiom* $(x_h=0)\vee(x_h=1)$, or follows from earlier lines by

- **Resolution:** from $A\vee L_1$ and $B\vee L_2$, with $L_1,L_2$ linear equations, derive $A\vee B\vee(L_1+L_2)$, or $A\vee B\vee(L_1-L_2)$;
- **Weakening:** from $A$ derive $A\vee L$ for any linear equation $L$;
- **Simplification:** from $A\vee(0=k)$ with $k\ne0$ derive $A$.

An R(lin) refutation of $K$ is a proof of the empty disjunction, and its size is the total size of its lines.

**Proposition.** R(lin) is a sound and complete Cook-Reckhow refutation system for unsatisfiable CNF formulas (translated as above); moreover it polynomially simulates resolution.

## Expansion

Resolving $\widetilde A\vee(x_i=1)$ against $\widetilde B\vee(x_i=0)$ by subtraction gives $\widetilde A\vee\widetilde B\vee(0=1)$, and simplification removes $(0=1)$, so each resolution step costs a linear overhead; checking each inference is polynomial time. R(lin) is in fact implicationally complete. A disjunction of equations that differ only in their free terms can express a linear inequality, or parity, which explains its strength: it polynomially simulates resolution over cutting-planes inequalities with polynomially bounded coefficients and Res($2$), and it has a natural [fragment R$^0$(lin)](r0-lin-fragment.md) that depth-3 multilinear proofs can simulate.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Resolution derivability](../../../propositional-logic/resolution/resolution-derivable.md)

## Proof depends on

None.

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Sections 3.1-3.2, Definition 3.1, Proposition 1; Theorem 11; Theorem 38).
