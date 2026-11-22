# Normal basis coordinates turn Frobenius into rotation

Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then $\Phi$ is
a bijection, and for every $a \in F^n$,

$$\Phi(a_0, \dots, a_{n-1})^q = \Phi(a_{n-1}, a_0, a_1, \dots, a_{n-2}),$$

that is, raising to the $q$-th power rotates the coordinates one step.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 28, with `Φ` as defined in Section 9 of the arXiv text (`jis-2026-26.4.6-lem-28`).
