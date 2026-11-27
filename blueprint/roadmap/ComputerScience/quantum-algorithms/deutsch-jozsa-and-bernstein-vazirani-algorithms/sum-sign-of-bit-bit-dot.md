# Orthogonality of the parity characters

For $u \in \mathbb{Z}_2^n$,

$$\sum_{x \in \mathbb{Z}_2^n} (-1)^{u\cdot x} = \begin{cases} 2^n & u = 0,\\ 0 & u \neq 0. \end{cases}$$

If $u_i = 1$, translating $x$ by the $i$-th basis vector flips every sign, so the sum equals its own
negative. This is the orthonormality of the parity basis used by Bernstein and Vazirani
(Section 8.4).

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
