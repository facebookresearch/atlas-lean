# Clarke's incompleteness theorem

No Hoare axiom system $H$ is sound and complete in the sense of Cook for a programming language that allows (i) procedures as parameters of procedure calls, (ii) recursion, (iii) static scope, (iv) global variables and (v) internal procedures. The incompleteness already holds when only procedure identifiers are passed as procedure parameters, without self-application or sharing.

The proof takes a finite interpretation $I$ with at least two elements. Its assertion language is expressive, and truth of its formulas is decidable, so the proof system $T$ meets Cook's hypotheses. Since $\{\mathit{true}\}\, S\, \{\mathit{false}\}$ is true exactly when $S$ diverges from the initial values of its global variables, a sound and complete $H$ would allow the programs that diverge from their initial values to be enumerated by enumerating proofs (checking each use of the rule of consequence with the decision procedure for $I$), while the programs that halt can be enumerated by running them; together these would decide the halting problem. Clarke also shows that, with sharing and self-application disallowed, modifying any one of the five features (no procedure parameters, no recursion, no global variables, dynamic scope, or no internal procedures) gives a language with a sound and complete axiom system.

## Depends on

- [Algol-like programs with procedure parameters](algol-like-programs-with-procedure-parameters.md)

## Proof depends on

- [Assertion languages over finite interpretations are expressive](assertion-languages-over-finite-interpretations-are-expressive.md)
- [Halting is undecidable with procedure parameters](halting-is-undecidable-with-procedure-parameters.md)

## Sources

- E. M. Clarke, "Programming language constructs for which it is impossible to obtain good Hoare axiom systems", *Journal of the ACM* 26(1):129–147, 1979, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Papers%20In%20Refereed%20Journals/79_impossible_hoareaxiom.pdf>, Section 3, Theorem 3.1, and Section 4, Table I.
