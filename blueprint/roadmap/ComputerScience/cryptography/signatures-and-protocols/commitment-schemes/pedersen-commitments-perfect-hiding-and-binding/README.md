# Pedersen commitments: perfect hiding, and binding from the discrete logarithm

- [Pedersen commitment value](commit-value.md)

## The scheme and perfect hiding

- [Pedersen commitment scheme](scheme.md)
- [Accepted openings of a Pedersen commitment](accepts-iff.md)
- [Pedersen commitments are uniform](commitment-dist-eq-uniform.md)
- [Perfect hiding of Pedersen commitments](perfectly-hiding.md)
- [Perfect hiding in a group of prime order](perfectly-hiding-of-prime-card.md)
- [Pedersen commitments are not perfectly binding](not-perfectly-binding.md)

## Binding extraction

- [Discrete-logarithm extractor from two openings](extract.md)
- [Exponentiation from an element of prime order has trivial kernel](eq-zero-of-gpow-eq-one.md)
- [Two openings reveal the discrete logarithm](extract-spec.md)

## Parameter generation

- [Pedersen parameter generation](param-gen.md)
- [Generated parameters are powers of g by units](exists-of-mem-support-param-gen.md)
- [Generated parameters have order dividing q](pow-eq-one-of-mem-support-param-gen.md)
- [Generated parameters are not the identity](ne-one-of-mem-support-param-gen.md)
- [Every generated parameter gives a perfectly hiding scheme](perfectly-hiding-of-mem-support.md)

## Computational binding from the discrete logarithm

- [Discrete-logarithm adversary for Pedersen parameters](dladversary.md)
- [Discrete-logarithm experiment with Pedersen parameters](dl-game.md)
- [Discrete-logarithm advantage with Pedersen parameters](dl-advantage.md)
- [Binding experiment for Pedersen commitments](binding-game.md)
- [Binding advantage against Pedersen commitments](binding-advantage.md)
- [Discrete-logarithm adversary from a binding adversary](reduction.md)
- [Computational binding of Pedersen commitments from the discrete logarithm](binding-advantage-le.md)
