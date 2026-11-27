# Temporally safe HyperLTL with LTL specifications is Σ¹₁-complete

Once an arbitrary LTL property that every trace must satisfy is added, satisfiability of temporal safety HyperLTL jumps to $\Sigma^1_1$-complete, already for one universal trace quantifier followed by existential ones and a single globally operator.

**Theorem (Beutner, Carral, Finkbeiner, Hofmann and Krötzsch).** The satisfiability problem for [specifications](temporal-safety-and-temporal-liveness-hyperltl.md) $(\psi, \varphi)$, with $\psi$ an arbitrary LTL formula and $\varphi$ a HyperLTL formula of the form $\forall\exists^*.\,G$, is $\Sigma^1_1$-complete: the set of such satisfiable specifications is in $\Sigma^1_1$ and every $\Sigma^1_1$ set many-one reduces to it. Here $\varphi = \forall\pi_1\exists\pi_2 \dots \exists\pi_m.\,(G\phi) \wedge \phi'$ with $\phi$ and $\phi'$ free of temporal operators, so $\varphi$ is temporal safety; the problem asks for a nonempty set of traces all satisfying $\psi$ that satisfies $\varphi$.

If $\psi$ is itself a safety property, it can be merged into $\varphi$ and the problem stays co-r.e.; the jump comes from non-safety LTL specifications.

## Depends on

- [Temporal safety and temporal liveness HyperLTL formulas](temporal-safety-and-temporal-liveness-hyperltl.md)

## Proof depends on

- [HyperLTL satisfiability is Σ¹₁-complete](../satisfiability-of-hyperltl-and-hyperctl-star/hyperltl-satisfiability-is-sigma-1-1-complete.md)
- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

Membership in $\Sigma^1_1$ follows from the $\Sigma^1_1$ upper bound for HyperLTL satisfiability (Fortin, Kuijer, Totzke and Zimmermann). For hardness the proof encodes recurring computations of nondeterministic two-counter machines. A counter value $v$ is encoded by a proposition holding exactly at position $v$, and a third counter decreasing at each step forces the initial instruction to recur. Each trace carries two consecutive configurations on disjoint copies of the propositions; the LTL specification $\psi$ checks that the second is a successor of the first and that the third counter decreases or the initial instruction occurs, and the $\forall\exists$ formula requires an initial configuration and, for each trace $\pi$, a trace $\pi'$ whose first configuration equals the second configuration of $\pi$, a condition expressible with one $G$.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Theorem 3.11 of arXiv:2205.15138v1 and its proof sketch (full proof in Appendix A).
