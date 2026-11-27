# Rabin cryptosystem

Rabin's public-key function $E_{n,b}(x) = x(x + b) \bmod n$, for $n = pq$ a product of two primes,
and his theorem that inverting it is as hard as factoring $n$: any algorithm that returns one square
root of each square modulo $n$ factors $n$ with probability $1/2$ per random trial.

- [The Rabin function](rabin-function.md)
- [Inverting the Rabin function extracts square roots](rabin-function-two-mul.md)
- [Square roots modulo a prime p ≡ 3 (mod 4)](pow-add-one-div-four-sq.md)
- [The gcd with pq is a prime factor exactly when one prime divides](gcd-mul-mem-iff.md)
- [A successful trial factors pq](is-factorization-of-gcd-mem.md)
- [A square-root oracle factors pq on exactly half of the units](two-mul-card-gcd-mem-eq-totient.md)
- [A partial square-root oracle factors pq on half of its domain](two-mul-card-gcd-mem-eq-card.md)

## Related topics

- [RSA cryptosystem](../rsa-cryptosystem/README.md): the trapdoor function on the same moduli
  $n = pq$; Rabin (1979, abstract) contrasts it with his function, noting that breaking RSA is at
  most as hard as factoring but was not known to be equivalent to it.
- [Goldwasser–Micali encryption](../goldwasser-micali-encryption/README.md): another scheme on
  $n = pq$ whose security rests on squares modulo $n$ (quadratic residuosity).
- [Miller–Rabin primality test](../../../algebraic-and-numerical-algorithms/miller-rabin-primality-test/README.md): how the primes $p$, $q$ of a key are generated.
