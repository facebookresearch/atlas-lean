# Error probability of maximum-likelihood decoding, ties counted as errors

Let $C = (x_1, \dots, x_M)$ be a code of $M$ words of length $N$ for a memoryless channel $W$. When
$x_m$ is sent, the decoder errs on every output $y$ for which some other code word is at least as
likely: $W^N(y \mid x_m) \le W^N(y \mid x_{m'})$ for some $m' \ne m$. The error probability is

$$P_{e,m}(C) = \sum_{y} W^N(y \mid x_m)\, \mathbf 1\big[\exists\, m' \ne m,\ W^N(y \mid x_m) \le W^N(y \mid x_{m'})\big].$$

Counting every tie as an error, as Gallager does, makes $P_{e,m}(C)$ an upper bound for the error
probability of every maximum-likelihood decoder, whatever its tie-breaking rule, so bounds on it
hold for all of them.

## Background

- [Block transition probability of a memoryless channel](block-transition.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equations (2)–(5).
