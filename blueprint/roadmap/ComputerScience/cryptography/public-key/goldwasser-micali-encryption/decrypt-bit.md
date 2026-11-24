# Goldwasser–Micali trapdoor decryption of one bit

Given the factors $p$ and $q$ and a residue $c$ modulo $N$, output $0$ if
$c^{\lfloor p/2 \rfloor} \equiv 1 \pmod p$ and $c^{\lfloor q/2 \rfloor} \equiv 1 \pmod q$, and $1$
otherwise, where $c$ is reduced modulo $p$ and $q$ through its representative in $\{0, \dots, N - 1\}$.
Only two modular powers are computed.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4 (decoding by testing quadratic residuosity) and Lemma 2.
