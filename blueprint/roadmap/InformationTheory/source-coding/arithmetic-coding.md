# Arithmetic coding

Fix a block length $n$ known to encoder and decoder, a finite alphabet with a fixed order, and a probability
assignment $q$ on blocks $x^n$ with rational values computable from the prefix. For every block with $q(x^n) > 0$, the
arithmetic encoder, which orders blocks lexicographically and maps $x^n$ to the binary expansion of the leftmost
largest dyadic interval $[m 2^{-k}, (m+1) 2^{-k})$ contained in $[F(x^n), F(x^n) + q(x^n))$, where
$F(x^n) = \sum_{y^n < x^n} q(y^n)$ is computed in exact rational arithmetic, outputs a binary string of length at most
$\lceil \log_2 (1/q(x^n)) \rceil + 1$ from which the decoder recovers $x^n$, and the codewords of the blocks with positive
probability form a prefix-free set. Blocks of probability zero are not encoded. Variable-length inputs need an
explicit termination convention (an end symbol or a transmitted length), which this statement does not cover.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Computable encoder/decoder contract.

## Depends on

- [Prefix-free code](prefix-codes/is-prefix-free.md)

## Related topics

- [Kraft's inequality for prefix codes](kraft-mcmillan-lengths.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Lecture notes on information theory*, MIT 6.441, Spring 2016, Section 9.1 (the lexicographic
  intervals, the largest dyadic subinterval, and the prefix code with length at most
  $\lceil \log_2 (1/Q_{X^n}(x^n)) \rceil + 1$). <https://ocw.mit.edu/courses/6-441-information-theory-spring-2016/5d8f16adc3385c9ff2975b121bd620e4_MIT6_441S16_course_notes.pdf>
- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft),
  Section 13.1, encoder (13.1). <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
