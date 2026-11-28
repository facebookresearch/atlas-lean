# MSO with the ultimately periodic quantifier is undecidable on ω-words

Satisfiability over $\omega$-words of monadic second-order logic extended by a quantifier over ultimately periodic sets is undecidable, answering a question of Bojańczyk and Colcombet.

**Theorem (Bojańczyk, Daviaud, Guillon, Penelle and Sreejith).** Satisfiability over $\omega$-words is undecidable for [MSO+P](mso-with-the-ultimately-periodic-quantifier.md): no algorithm decides, given an MSO+P sentence over a finite alphabet, whether some $\omega$-word satisfies it (Theorem 1.4 of the source).

Since the letter predicates of an $\omega$-word can be quantified existentially as sets, the MSO+P theory of $(\mathbb{N}, <)$ is undecidable as well, in contrast with plain MSO, which is decidable by Büchi's theorem.

## Depends on

- [Monadic second-order logic with the ultimately periodic quantifier](mso-with-the-ultimately-periodic-quantifier.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The MSO+U theory of the natural numbers with order is undecidable](the-mso-u-theory-of-the-natural-numbers-with.md)

## Expansion

The main theorem of the source shows that MSO+U and MSO+U$_1$ define the same languages of $\omega$-words, with effective translations both ways; since MSO+U has undecidable satisfiability, so does MSO+U$_1$. The predicate $\mathsf{U}_1$ is definable with $\mathsf{P}$: a set $X$ satisfies $\mathsf{U}_1(X)$ iff for every infinite ultimately periodic set $Y$ there are two positions of $Y$ not separated by a position of $X$. Hence every MSO+U$_1$ sentence can be effectively rewritten into an MSO+P sentence true on the same $\omega$-words, and a decision procedure for MSO+P would decide MSO+U$_1$.

## Sources

- M. Bojańczyk, L. Daviaud, B. Guillon, V. Penelle and A. V. Sreejith, "Undecidability of a weak version of MSO+U", *Logical Methods in Computer Science* 16(1), 2020, paper 12, doi:10.23638/LMCS-16(1:12)2020; read as arXiv:1807.08506v5, <https://arxiv.org/abs/1807.08506v5>: the theorem on MSO+P (label thm:periodic) and the main theorem (label thm:main) in Section 1, with the reduction in the proof of that theorem in Section 4 ("How MSO+U may talk about ultimate periodicity").
