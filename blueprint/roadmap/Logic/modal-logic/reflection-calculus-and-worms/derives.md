# The Reflection Calculus RC

RC derives sequents $A \vdash B$ between strictly positive formulas from the axioms and rules

1. $A \vdash A$; $A \vdash \top$; from $A \vdash B$ and $B \vdash C$ infer $A \vdash C$;
2. $A \wedge B \vdash A$; $A \wedge B \vdash B$; from $A \vdash B$ and $A \vdash C$ infer
   $A \vdash B \wedge C$;
3. from $A \vdash B$ infer $\langle n \rangle A \vdash \langle n \rangle B$;
   $\langle n \rangle\langle n \rangle A \vdash \langle n \rangle A$;
4. $\langle m \rangle\langle n \rangle A \vdash \langle n \rangle A$ and
   $\langle n \rangle\langle m \rangle A \vdash \langle n \rangle A$ for $m \ge n$;
5. $\langle m \rangle A \wedge \langle n \rangle B \vdash \langle m \rangle(A \wedge \langle n \rangle B)$
   for $m > n$;
6. $\langle m \rangle A \vdash \langle n \rangle A$ for $m > n$ (monotonicity).

Axioms 1–5 form the system RJ; axiom 6 makes it RC. Axioms 4 follow from axioms 3 and 6. The
modalities range over $\mathbb{N}$ (the source's $\mathrm{RC}_S$ with $S = \mathbb{N}$).
Dashkov showed that RC axiomatizes exactly the sequents $A \vdash B$ with $\mathrm{GLP} \vdash A \to B$.

## Background

- [Strictly positive formulas](formula.md): the formulas that RC's sequents relate.

## Sources

- L. D. Beklemishev, "Positive provability logic for uniform reflection principles", arXiv:1304.4396v3 (2013), *Annals of Pure and Applied Logic* 165 (2014), Section 2 (axioms 1–6; Dashkov's theorem as reported there).
