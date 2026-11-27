# Equality of one-variable sine expressions with absolute value is undecidable

No algorithm decides whether two expressions built from the integers and x by addition, multiplication, sine and absolute value define the same real function, because |f| = f exactly when f is everywhere nonnegative.

**Theorem (Richardson).** Let $\mathscr S$ be the set of functions $\mathbb R \to \mathbb R$ built from the integers and $x$ using addition, multiplication and composition with $\sin$. It is impossible to decide, given $f \in \mathscr S$, whether $|f|$ and $f$ are the same function. Hence equality of functions defined by expressions built from the integers and $x$ using addition, multiplication, $\sin$ and the absolute value is undecidable.

The same holds with several variables for expressions in $\mathbb Z[x_1, \ldots, x_n, \sin x_1, \ldots, \sin x_n]$ together with the absolute value.

## Depends on

None.

## Proof depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](sign-and-zeros-of-one-variable-sine-terms.md)

## Expansion

The functions $|f|$ and $f$ agree everywhere exactly when $f$ is everywhere nonnegative, so a decision procedure for equality would decide nonnegativity for $\mathscr S$.

## Sources

- Daniel Richardson, "Some undecidable problems involving elementary functions of a real variable", *Journal of Symbolic Logic* 33(4), 1968, pp. 514–520, <https://doi.org/10.2307/2271358>: Section 2, Theorem Two (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Section 9.2 ("Equality of functions") of that version.
