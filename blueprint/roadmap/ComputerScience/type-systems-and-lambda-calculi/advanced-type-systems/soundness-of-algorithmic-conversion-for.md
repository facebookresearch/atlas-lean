# Soundness of algorithmic conversion for dependent type theory

For Martin-Löf type theory with dependent function types with $\eta$, natural numbers and one universe à la Russell, with declarative typing and judgmental equality, the type-directed algorithmic conversion checker is sound: if it accepts $\Gamma \vdash A \sim B$ for well-formed types, then $\Gamma \vdash A = B$ holds, and likewise for terms at a type.

## Depends on

- [Pure type systems and the calculus of constructions](pure-type-systems-and-the-calculus-of.md)
- [The type theory λΠUN](martin-lof-type-theory-with-one-universe/the-type-theory-lambda-pi-u-n.md)
- [Algorithmic conversion for λΠUN](martin-lof-type-theory-with-one-universe/algorithmic-conversion-for-lambda-pi-u-n.md)

## Proof depends on

- [Π-injectivity and syntactic validity for λΠUN](martin-lof-type-theory-with-one-universe/pi-injectivity-and-syntactic-validity-for-lambda-pi-u-n.md)

## Expansion

This page becomes ready once:

- Neutral type equality and universe membership for λΠUN (Theorems 3.33 and 3.34 of the source) (proof prerequisite; not yet stated)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.2, Lemma 4.3 (soundness).
