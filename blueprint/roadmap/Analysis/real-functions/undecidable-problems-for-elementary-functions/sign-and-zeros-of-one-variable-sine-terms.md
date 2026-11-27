# Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable

For real functions of one variable built from the integers and x by addition, multiplication and composition with sine, no algorithm decides whether such a function is everywhere nonnegative, whether it is everywhere positive, or whether it has a zero. The constant π is not needed.

**Theorem (Laczkovich).** Let $\mathscr S$ be the set of functions $\mathbb R \to \mathbb R$ built from the integers and $x$ using addition, multiplication and composition with $\sin$. Given $f \in \mathscr S$ (as an expression), it is impossible to decide whether $f$ is everywhere nonnegative. It is also impossible to decide whether $f$ is everywhere positive, and whether $f$ has a zero.

More precisely, there are functions $F_a \in \mathscr S$ depending computably on an integer parameter $a$ such that either $F_a(x) > 1$ for all $x \in \mathbb R$, or $F_a$ takes values less than $-1$ and values greater than $1$, and it is impossible to decide which, given $a$. This improves Richardson's one-variable theorem, which used $\pi$ among the constants.

## Depends on

None.

## Proof depends on

- [Everywhere positivity of polynomials in the variables and their sines is undecidable](sign-of-polynomials-in-variables-and-sines.md)

## Expansion

Laczkovich's variant of the several-variable theorem replaces $\sin \pi x_i$ by $\sin x_i$. Composing a multivariable function with a function $h : \mathbb R \to \mathbb R^n$ with dense image, such as $h(x) = (x \sin x, x \sin x^3, \ldots, x \sin x^{2n-1})$ (used by Denef and Lipshitz), turns it into a function of one variable with the same sign behavior; the density of the image of $h$ and Laczkovich's variant with $\sin x_i$ in place of $\sin \pi x_i$ have no page here.

## Sources

- Miklós Laczkovich, "The removal of π from some undecidable problems involving elementary functions", *Proceedings of the American Mathematical Society* 131(7), 2003, pp. 2235–2240, <https://doi.org/10.1090/S0002-9939-02-06753-9>: Theorem 1 (cited after the survey below).
- Daniel Richardson, "Some undecidable problems involving elementary functions of a real variable", *Journal of Symbolic Logic* 33(4), 1968, pp. 514–520, <https://doi.org/10.2307/2271358>: Corollary to Theorem Two, the version with $\pi$ (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Theorem 9.4, the discussion before it (Laczkovich's variant and the function $h$) and the paragraph after it recording the functions $F_a$, in Section 9.1.3 of that version.
