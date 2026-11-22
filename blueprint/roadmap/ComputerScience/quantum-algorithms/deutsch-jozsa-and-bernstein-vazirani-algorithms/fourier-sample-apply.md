# Amplitudes of Fourier sampling

For $f : \mathbb{Z}_2^n \to \mathbb{Z}_2$, the amplitude of $|t\rangle$ in $H_n O_f H_n |0\cdots0\rangle$, where
$O_f |x\rangle = (-1)^{f(x)} |x\rangle$, is

$$2^{-n} \sum_{x} (-1)^{f(x) + t\cdot x} .$$

This is equation (3.6) of Cleve, Ekert, Macchiavello and Mosca with the normalisation restored, and the
special case of Fourier sampling with respect to $g = (-1)^f$ in Bernstein and Vazirani (Theorem 8.4.2:
outcome $s$ with probability $|\hat f(s)|^2$ for $f(x) = g(x)/2^{n/2}$).

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
