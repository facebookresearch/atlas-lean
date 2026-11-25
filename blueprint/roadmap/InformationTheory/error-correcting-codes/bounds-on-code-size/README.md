# Bounds on code size

How many codewords can a code of length $n$ over $q$ letters have if any two are at Hamming
distance at least $d$? Upper bounds come from packing (Hamming), projection (Singleton),
averaging distances (Plotkin) and list decoding (Elias–Bassalygo); the Gilbert–Varshamov bound
shows by a greedy covering argument that codes of rate $1 - H_q(\delta)$ and relative distance
$\delta$ exist, linear ones included.

## Hamming balls

- [Closed Hamming ball](ball.md)
- [Size of a Hamming ball](card-ball.md)
- [Size of a Hamming ball of fixed-length words](card-ball-fin.md)
- [Volume of a Hamming ball, entropy upper bound](sum-choose-mul-pow-le-exp.md)
- [The central binomial term](central-term-ge.md)
- [The largest term of a Hamming-ball volume](choose-mul-pow-ge.md)
- [Volume of a Hamming ball, entropy lower bound](sum-choose-mul-pow-ge-exp.md)

## Upper bounds

- [Singleton bound](singleton-bound.md)
- [Hamming bound](hamming-sphere-packing-bound.md)
- [Disagreeing pairs in a coordinate](disagreeing-pairs-in-a-coordinate.md)
- [Plotkin bound](plotkin-bound.md)
- [Elias–Bassalygo bound (alphabet-free form)](elias-bassalygo-bound.md)

## The Gilbert–Varshamov bound

- [A maximal code is covering](bi-union-ball-eq-univ-of-maximal.md)
- [Gilbert–Varshamov bound](exists-code-pow-le-card-mul-sum.md)
- [Gilbert–Varshamov bound, rate form](exists-code-exp-le-card.md)
- [One greedy step](exists-extend.md)
- [Gilbert–Varshamov bound for linear codes](exists-linear-code-finrank-eq.md)

## Related topics

- [Linear codes](../linear-codes/README.md): the Singleton and Hamming bounds specialised to linear codes.
- [Reed–Solomon codes](../reed-solomon-codes/README.md): codes meeting the Singleton bound with equality (MDS codes).
- [CSS codes](../../../QuantumInformation/quantum-error-correction/css-codes/README.md): quantum codes whose parameters are governed by those of two classical linear codes.
