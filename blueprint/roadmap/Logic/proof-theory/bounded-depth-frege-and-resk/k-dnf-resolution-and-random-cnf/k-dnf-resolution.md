# $k$-DNF resolution Res($k$)

Res($k$) is the extension of resolution whose lines are $k$-DNFs, disjunctions of conjunctions of at most $k$ literals, with weakening, AND-introduction, AND-elimination and a cut rule that resolves a conjunction of literals against the disjunction of their negations. Res($1$) is resolution.

A *term* is a conjunction of literals and a $k$-*DNF* is a disjunction of terms each with at most $k$ literals. A Res($k$) proof (refutation) of an unsatisfiable CNF $\varphi$ is a sequence of $k$-DNFs $C_1,\dots,C_s$ with $C_s=\emptyset$, the empty formula, in which each $C_i$ is a clause of $\varphi$ or follows from earlier lines by one of the rules

$$
\frac{F}{F\vee\ell}\qquad
\frac{F\vee\ell_1\quad\cdots\quad F\vee\ell_w}{F\vee\bigwedge_{i=1}^{w}\ell_i}\qquad
\frac{F\vee\bigwedge_{i=1}^{w}\ell_i}{F\vee\ell_i}\qquad
\frac{F\vee\bigwedge_{i=1}^{w}\ell_i\qquad G\vee\bigvee_{i=1}^{w}\neg\ell_i}{F\vee G}
$$

(weakening, AND-introduction, AND-elimination and cut), where every line, and so every introduced term, is a $k$-DNF. The size of the proof is taken to be the number $s$ of lines; measuring instead the total size of the lines gives a weaker notion for lower bounds, so lower bounds for the line count also hold for total size.

## Expansion

Res($k$) was introduced by Krajíček. It sits between [resolution](../../../propositional-logic/resolution/resolution-derivable.md) and bounded-depth Frege: its lines are depth-2 formulas, so it is a subsystem of depth-2 Frege, and for $k=2$ it is [simulated by resolution over linear equations](../resolution-over-linear-equations/r-lin-stronger-than-r0-lin.md); that simulation uses Raz and Tzameret's formulation of Res($2$), whose proof size is the total number of literals in its lines rather than the number of lines. Lower bounds for random CNFs in Res($k$) mark a current frontier for subsystems of Frege; see the [expansion-based lower bound](res-k-lower-bound-from-boundary-expansion.md). Res($k$) is also [not automatable unless P = NP](../../automatability-of-proof-systems/garlik-resk.md).

## Depends on

- [Resolution derivability](../../../propositional-logic/resolution/resolution-derivable.md)

## Proof depends on

None.

## Sources

- Anastasia Sofronova and Dmitry Sokolov, "A Lower Bound for k-DNF Resolution on Random CNF Formulas via Expansion", *40th Computational Complexity Conference (CCC 2025)*, LIPIcs vol. 339, paper 32, 2025, https://doi.org/10.4230/LIPIcs.CCC.2025.32; numbering as in the [ECCC Report TR22-054 edition](https://eccc.weizmann.ac.il/report/2022/054/) (Section 2, definition of Res(k)).
- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Definition 6.4 of Res(2)).
