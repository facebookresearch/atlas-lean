# Seed recovery distinguishes the one-step linear congruential generator

For the one-step linear congruential generator, the deterministic test that, on input $(r, s')$, computes $s = a^{-1}(s' - b) \bmod q$ and accepts iff $\lfloor s/w \rfloor = r$ runs in time polynomial in the bit lengths of the parameters and has distinguishing advantage exactly

$$1 - \frac{1}{|R|}, \qquad |R| = \lfloor (q-1)/w \rfloor + 1.$$

In particular the generator is insecure whenever $w < q$, but the advantage is $0$ when $w \ge q$.

## Proof sketch

On generator outputs the test always accepts. On uniform $(r, s')$, the recovered $s$ is uniform and independent of $r$, so the test accepts with probability exactly $1/|R|$.

## Depends on

- [Linear congruential generator](linear-congruential-generator.md)
- [PRG advantage](../pseudorandom-generators/prg-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
