# Carry-less multiplication by the window method

Let $w$ be the word size and let polynomials over $\mathbb{F}_2$ of degree below $w$ be stored as $w$-bit words, bit $i$ holding the coefficient of $x^i$. For a window size $s \ge 1$, the *window method* (Brent, Gaudry, Thomé and Zimmermann, Section 1.1) computes the carry-less product $a(x)\, b(x)$ as follows: store in a table the products of $b$ with all $2^s$ polynomials of degree below $s$, each in two words; then scan the bits of $a$, $s$ at a time, and accumulate by exclusive or the table entry selected by each group of bits, shifted to the position of that group. Once the table of $2^s$ entries is built, the product, of degree below $2w - 1$, takes $\lceil w/s \rceil$ table lookups, together with as many two-word shifts and exclusive ors.

## Proof sketch

Carry-less multiplication is bilinear over $\mathbb{F}_2$: writing $a = \sum_j a_j x^{js}$ with each $a_j$ of degree below $s$ gives $a b = \sum_j (a_j b)\, x^{js}$, so the product is the exclusive or of the shifted table entries $a_j b$. Storing each entry in two words keeps the high coefficients of $a_j b$; the source's single-word variant stores the entries modulo $x^w$ and restores the missing high coefficients by a repair step.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- R. P. Brent, P. Gaudry, E. Thomé and P. Zimmermann, "Faster Multiplication in GF(2)[x]", Algorithmic Number Theory (ANTS-VIII), Lecture Notes in Computer Science 5011, Springer, 2008, Section 1.1 (the window method, algorithm mul1, footnote 1).
