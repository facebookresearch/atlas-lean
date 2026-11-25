# The residuosity experiment

For a fixed modulus $N$, a distribution of keys $(y, (p, q))$, a distribution of coins and a
distinguisher $D$, the experiment in world $b$ draws a key, coins $r$ and a uniform unit $x$ modulo
$N$, and outputs $D(y, z, r)$ where $z = x^2$ if $b = 0$ and $z = y x^2$ if $b = 1$. When $y$ is a
non-residue with Jacobi symbol $+1$, the element $y x^2$ is a uniformly random non-residue with Jacobi
symbol $+1$, so the experiment asks to tell random quadratic residues from random such non-residues.
As stated, the experiment is the distribution of
Goldwasser–Micali ciphertexts of $0$ and $1$ (the distinguisher also sees $y$), so reductions to it
are close to definitional.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 3.2 (the quadratic residuosity problem and assumption), stated here as a concrete
  experiment for one modulus.
