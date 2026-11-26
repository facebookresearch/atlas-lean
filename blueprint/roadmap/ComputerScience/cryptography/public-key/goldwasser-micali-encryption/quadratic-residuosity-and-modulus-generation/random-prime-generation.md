# Random prime generation with the Miller–Rabin test

The prime generator that, on input $1^n$, draws up to $3n^2$ uniform $n$-bit odd candidates, runs the Miller–Rabin test with $n$ independent rounds on each, and returns the first candidate that passes, satisfies: (a) it returns a composite number with probability at most $3n^2\,4^{-n} \le 3n^2\,2^{-n}$; (b) using that the fraction of primes among $n$-bit integers is at least $1/(3n)$ for large $n$ (Bertrand-type density bounds), it fails to return any number with probability at most $e^{-n}$; (c) it runs in polynomial time. Generating RSA moduli as products of two such primes inherits these bounds.

## Proof sketch

(a) Each composite candidate passes $n$ rounds with probability at most $4^{-n}$; union over the candidates. (b) All $3n^2$ candidates are composite with probability at most $(1 - 1/(3n))^{3n^2} \le e^{-n}$.

## Depends on

- [The Miller–Rabin test](../../../../algebraic-and-numerical-algorithms/miller-rabin-primality-test/miller-rabin.md)
- [RSA key](../../rsa-cryptosystem/key.md)

## Sources

- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
