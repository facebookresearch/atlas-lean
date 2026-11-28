# Type checking for DFuzz is undecidable

Type checking for DFuzz, the linear indexed type system for differential privacy whose function types carry polynomial sensitivity annotations over size variables, is undecidable, because subtyping between such types encodes Hilbert's tenth problem.

**DFuzz.** DFuzz (Gaboardi, Haeberlen, Hsu, Narayan and Pierce) extends PCF with linear types $!_R \sigma \multimap \tau$ indexed by sensitivities. Indices are numeric constants, index variables of kind $\mathbb{N}$ (sizes, $S ::= i \mid 0 \mid S + 1$) or of kind $\mathbb{R}$ (sensitivities in $\mathbb{R}^{\ge 0} \cup \{\infty\}$), sums and products; terms include index abstraction $\Lambda i : \kappa.\, e$ and application $e[R]$, singleton types $\mathbb{N}[S]$ and $\mathbb{R}[R]$, and dependent pattern matching on $\mathbb{N}[S]$. Judgments $\Phi; \Delta \mid \Gamma \vdash e : \sigma$ carry a constraint environment $\Phi$, an index environment $\Delta$ and an environment $\Gamma$ of sensitivity-annotated variables; subtyping $\sigma \sqsubseteq \tau$ compares sensitivity annotations by the order on indices, universally over the index variables in scope.

**Theorem.** The type checking problem for DFuzz, as presented in the source (given an environment $\Gamma$, a term $e$ and a type $\sigma$, does a derivation of $\emptyset; \emptyset \mid \Gamma \vdash e : \sigma$ exist?), is undecidable. Instances are finite syntax; the problem stays undecidable when every numeric constant in the input is a natural number, since the proof encodes the inequality $\forall \vec{i} \in \mathbb{N}^n.\ P(\vec{i}) \ge Q(\vec{i})$ for polynomials $P, Q$ with coefficients in $\mathbb{N}$ (Lemma 9) as a subtyping question between types over size variables.

## Depends on

- [PCF terms](../../programming-language-semantics/pcf-and-computational-adequacy/tm.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By Hilbert's tenth problem it is undecidable, given polynomials $P, Q$ in $n$ variables with coefficients in $\mathbb{N}$, whether $P(\vec{i}) \ge Q(\vec{i})$ for all $\vec{i} \in \mathbb{N}^n$ (Lemma 9 of the source): $P$ has a zero in $\mathbb{N}^n$ iff not $P^+(\vec{i}) \ge P^-(\vec{i}) + 1$ for all $\vec{i}$, where $P^2 = P^+ - P^-$ with $P^\pm$ having nonnegative coefficients. With $\tau_Q = \forall \vec{i}.\, !_0\, \mathbb{N}^n[\vec{i}] \multimap\, !_{Q(\vec{i})} \mathbb{R} \multimap \mathbb{R}$ and $\tau_P$ likewise, $\tau_Q \sqsubseteq \tau_P$ holds iff $P \ge Q$ on $\mathbb{N}^n$. A recursive function using dependent pattern matching multiplies a real by $Q(\vec{v})$; its minimal type is $\tau_Q$, so checking it against $\tau_P$ decides the inequality. The undecidability carries over to the extension EDFuzz, for which the source gives a type checking algorithm relative to an oracle for subtyping constraints.

## Sources

- Arthur Azevedo de Amorim, Emilio Jesús Gallego Arias, Marco Gaboardi and Justin Hsu, "Really natural linear indexed type checking", *Proceedings of the 26th International Symposium on Implementation and Application of Functional Languages (IFL 2014)*, ACM, 12 pages, 2014, <https://doi.org/10.1145/2746325.2746335>; read as arXiv:1503.04522v1, <https://arxiv.org/abs/1503.04522v1>: Section 2 (the DFuzz system), Definition 4 (the type checking problem, stated there for the extension EDFuzz and used in the same form for DFuzz), Lemma 9 and Theorem 10 of that version.
- Marco Gaboardi, Andreas Haeberlen, Justin Hsu, Arjun Narayan and Benjamin C. Pierce, "Linear dependent types for differential privacy", *Proceedings of the 40th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2013)*, 357–370, 2013, <https://doi.org/10.1145/2429069.2429113>: the original DFuzz system, used here as presented in Section 2 of the version of the first source read.
