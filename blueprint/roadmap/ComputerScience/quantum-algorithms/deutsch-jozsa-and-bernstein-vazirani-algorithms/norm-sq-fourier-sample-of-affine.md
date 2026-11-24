# The Bernstein–Vazirani algorithm outputs $s$ with certainty

If $f(x) = s\cdot x + b$ for all $x$, then measuring $H_n O_f H_n |0\cdots0\rangle$ in the computational
basis gives the outcome $t$ with probability $1$ if $t = s$ and $0$ otherwise (Born rule: the squared
modulus of the amplitude).

## Informally uses

- [Bernstein–Vazirani algorithm](fourier-sample-of-affine.md): the final state is $(-1)^b |s\rangle$.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
