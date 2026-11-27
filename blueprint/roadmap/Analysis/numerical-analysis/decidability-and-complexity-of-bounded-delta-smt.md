# Decidability and complexity of bounded delta-SMT

This node collects the δ-decidability results of Gao, Avigad and Clarke for bounded first-order formulas over the
reals.

## Expansion

A sound expansion has separate pages for:

1. **δ-decidability.** For finite signatures of Type-2 computable functions that are total on the bounded domains used
   (including $\exp$, $\sin$ and solutions of Lipschitz ODEs with existence assumed on the domain), the bounded
   existential δ-SMT problem is decidable by a δ-complete procedure, for every rational $\delta > 0$.
2. **Complexity.** If all functions in a finite signature $F$ are in a Type-2 complexity class $\mathsf{C}$ with
   $\mathsf{P} \subseteq \mathsf{C} \subseteq \mathsf{PSPACE}$, the δ-SMT problem for a uniformly bounded class (all variable
   bounds inside one fixed interval $[l, u]$, every atom $f(x) = 0$ with $f \in F$) is in $\mathsf{NP}^{\mathsf{C}}$; it is
   $\mathsf{NP}$-complete for polynomial-time computable functions such as $+$, $\times$, $\exp$, $\sin$, and
   $\mathsf{PSPACE}$-complete for Lipschitz-continuous ODEs over compact domains. Formulas with quantifier alternation
   have their own bounds.
3. **Contrast.** Exact satisfiability over the reals with $\sin$ is undecidable.
4. **Interval constraint propagation.** For every rational $\delta > 0$ there is $\varepsilon > 0$ such that ICP with
   precision $\varepsilon$ is δ-complete on conjunctive bounded formulas if and only if its pruning operator is
   well-defined; the source's analysis of DPLL⟨ICP⟩ rests on this.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Turing machine.

## Depends on

- [delta-weakening and delta-complete decision procedures](delta-weakening-and-delta-complete-decision-procedures.md)

## Sources

- delta-Complete Decision Procedures for Satisfiability over the Reals — S. Gao, J. Avigad, E. M. Clarke, LNAI 7364, 2012, Theorem 3.1, Definition 3.3, Theorem 3.2, Corollaries 3.1 and 3.2, Theorem 4.2 and Sec. 4; undecidability with sine, Sec. 1. <http://www.cs.cmu.edu/~sicung/papers/cade2012.pdf>
