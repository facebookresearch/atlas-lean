# A valid Goldwasser–Micali key

A valid key for the modulus $N$ is a triple $(y, p, q)$ of a unit $y$ modulo $N$ that is not a square
and of distinct primes $p, q$ with $pq = N$. Goldwasser and Micali also require $y$ to have Jacobi
symbol $+1$, so that the public key does not reveal $y$ as a non-residue; correctness does not need
it, and the condition is not part of this definition. For example, $(2, 3, 5)$ is a valid key
for $N = 15$, and $2$ has Jacobi symbol $(2/3)(2/5) = 1$.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4.
