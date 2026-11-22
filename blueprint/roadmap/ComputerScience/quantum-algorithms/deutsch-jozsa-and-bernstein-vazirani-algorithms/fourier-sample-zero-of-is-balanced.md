# Deutsch–Jozsa algorithm, balanced case

If $f : \mathbb{Z}_2^n \to \mathbb{Z}_2$ is balanced (it takes the values $0$ and $1$ equally often),
the amplitude of $|0\cdots0\rangle$ in $H_n O_f H_n |0\cdots0\rangle$ is $0$, so measuring never gives
$0\cdots0$. If $f$ is constant, the outcome is $0\cdots0$ with probability $1$
([constant case](norm-sq-fourier-sample-zero-of-const.md)). One query therefore decides with
certainty whether a function promised to be constant or balanced is constant.

This is the one-query form of Cleve, Ekert, Macchiavello and Mosca (Section 3, after equation (3.6));
the original algorithm of Deutsch and Jozsa (1992) used two calls to the reversible oracle, as Cleve
et al. note. For $n \ge 1$, a deterministic classical algorithm needs $2^{n-1} + 1$ evaluations in the worst
case (Cleve et al., Section 3); for $n = 0$ every function is constant and no evaluation is
needed.

## Informally uses

- [Amplitudes of Fourier sampling](fourier-sample-apply.md): the amplitude of $|0\cdots0\rangle$ is $2^{-n} \sum_x (-1)^{f(x)}$, which vanishes when $f$ takes the values $0$ and $1$ equally often.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
