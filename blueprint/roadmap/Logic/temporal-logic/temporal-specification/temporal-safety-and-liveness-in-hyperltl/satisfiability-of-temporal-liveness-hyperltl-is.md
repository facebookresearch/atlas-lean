# Satisfiability of temporal liveness HyperLTL is Σ¹₁-hard

Unlike temporal safety, restricting HyperLTL bodies to liveness properties does not lower the complexity of satisfiability: it remains $\Sigma^1_1$-hard for formulas with one universal trace quantifier followed by existential ones.

**Theorem (Beutner, Carral, Finkbeiner, Hofmann and Krötzsch).** The satisfiability problem, whether some nonempty set of traces satisfies a given formula, is $\Sigma^1_1$-hard for $\forall\exists^*$ [temporal liveness HyperLTL formulas](temporal-safety-and-temporal-liveness-hyperltl.md): every $\Sigma^1_1$ set many-one reduces to the set of satisfiable closed HyperLTL formulas $\forall\pi_1\exists\pi_2 \dots \exists\pi_m.\,\phi$ whose body $\phi$ describes a liveness property. In particular the problem is undecidable and not arithmetical.

With the $\Sigma^1_1$ upper bound for HyperLTL satisfiability (Fortin, Kuijer, Totzke and Zimmermann), the problem is $\Sigma^1_1$-complete, as Table 1 of the source records.

## Depends on

- [Temporal safety and temporal liveness HyperLTL formulas](temporal-safety-and-temporal-liveness-hyperltl.md)

## Proof depends on

- [Temporally safe HyperLTL with LTL specifications is Σ¹₁-complete](temporally-safe-hyperltl-with-ltl-specifications.md)

## Expansion

The proof shows more (Theorem 4.3): every specification $(\psi, \varphi)$ with $\varphi = \forall^n\exists^m.\,\phi$ and $\psi$, $\phi$ satisfiable LTL formulas is equisatisfiable with an effectively computable $(\psi', \varphi')$ in which $\psi'$ is an LTL liveness property and $\varphi'$ a $\forall^n\exists^m$ temporal liveness formula. A fresh proposition $\dagger$ marks a start position: $\varphi'$ and $\psi'$ put the original bodies under $F$ at the last position where $\dagger$ holds, which makes the bodies liveness properties, and a minimal model can be taken in which this position is the same on all traces. By the $\Sigma^1_1$-hardness of specifications $(\psi, \forall\exists^*.\,G)$ (Theorem 3.11), and since a specification with at least one universal quantifier becomes an equivalent HyperLTL formula by moving $\psi$ into the body, satisfiability of $\forall\exists^*$ HyperLTL is $\Sigma^1_1$-hard; the transformation then carries this hardness to the temporal liveness fragment.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Theorem 4.2 of arXiv:2205.15138v1, proved through Theorem 4.3, and Section 1 and Table 1 (the $\Sigma^1_1$ upper bound recalled from Fortin, Kuijer, Totzke and Zimmermann, and completeness for the temporal liveness fragment).
