# List decoding

A code is list decodable from $e$ errors with list size $L$ if every Hamming ball of radius $e$
contains at most $L$ codewords. Allowing a short list instead of a unique answer lets a decoder
correct far more than half the minimum distance. The Johnson bound guarantees polynomial lists for
every code up to the radius $n - \sqrt{n(n-d)}$, which for Reed–Solomon codes of rate $R$ is a
$1 - \sqrt{R}$ fraction of errors; the list-decoding capacity theorem identifies $1 - H_q(\rho)$
as the best rate for a fraction $\rho$ of errors. The Guruswami–Sudan algorithm finds, for any
parameters $D, r$ with enough monomials, every message polynomial agreeing with the received word
in $t$ positions with $D < t r$. Guruswami, Rudra and Sudan (Theorem 12.2.12) choose $D$ and $r$ so
that it decodes up to the $1 - \sqrt{R}$ radius in polynomial time.

## Definition

- [List-decodable code](is-list-decodable.md)
- [List decodability is monotone in the list size](is-list-decodable-mono.md)

## The Johnson bound

- [Agreements of two words](card-filter-eq.md)
- [Johnson bound](johnson-bound.md)
- [Johnson bound, list size $n d$](card-le-mul-of-johnson.md)
- [Every code is list decodable up to the Johnson radius](is-list-decodable-of-johnson.md)

## List-decoding capacity

- [List-decoding capacity, achievability](exists-encoding-list-decodable.md)
- [List-decodable codes of rate $1 - H_q(\rho) - 1/L$](exists-is-list-decodable.md)
- [Some ball holds many codewords](exists-mul-card-filter-ge.md)
- [Volume of a Hamming ball, entropy lower bound](../bounds-on-code-size/sum-choose-mul-pow-ge-exp.md)
- [List-decoding capacity, converse](exists-many-in-ball.md)

## Guruswami–Sudan decoding of Reed–Solomon codes

- [Weighted degree bound](weighted-deg-le.md)
- [Ideal of a point of the plane](point-ideal.md)
- [Root of multiplicity $r$](has-root-mult.md)
- [Substitution respects the weighted degree](nat-degree-eval-le.md)
- [A root of multiplicity $r$ survives substitution](pow-dvd-eval-of-has-root-mult.md)
- [Translation of the plane](shift.md)
- [Multiplicity from the translated coefficients](has-root-mult-of-coeff.md)
- [Monomials of low total degree](low-monomials.md)
- [Number of multiplicity constraints](card-low-monomials.md)
- [Guruswami–Sudan interpolation step](exists-interpolant.md)
- [Guruswami–Sudan root-finding lemma](eval-eq-zero-of-agree.md)
- [$Y - P(X)$ divides the interpolating polynomial](x-sub-c-dvd-of-agree.md)
- [Guruswami–Sudan list decoding](exists-interpolant-dvd.md)
- [The list has at most $D / w$ polynomials](card-le-div-of-dvd.md)
- [Reed–Solomon codes are list decodable up to the Johnson radius](card-le-of-agree-ge.md)

## Related topics

- [Bounds on code size](../bounds-on-code-size/README.md): Hamming-ball volumes and the unique-decoding bounds that list decoding goes beyond.
- [Reed–Solomon codes](../reed-solomon-codes/README.md): the MDS codes whose unique decoding (Berlekamp–Welch) stops at half the minimum distance, and which the Johnson bound makes list decodable up to a $1 - \sqrt{R}$ fraction of errors.
- [Shannon's channel coding theorem](../../channel-coding/shannon-s-channel-coding-theorem/README.md): the capacity $1 - H_q(\rho)$ of the $q$-ary symmetric channel with crossover probability $\rho$ equals the list-decoding capacity for a fraction $\rho$ of worst-case errors (Guruswami, Rudra and Sudan, Section 7.4).
