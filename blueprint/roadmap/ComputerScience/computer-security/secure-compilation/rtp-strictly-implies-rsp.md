# Robust trace property preservation strictly implies robust safety preservation

**Theorem.** Every compilation chain that satisfies [robust trace property preservation](robust-trace-property-preservation.md) satisfies
[robust safety property preservation](robust-safety-property-preservation.md), but not conversely.

The implication is immediate. For strictness, take a target language that can produce infinite traces and a source language with the same partial programs whose
whole programs and contexts carry a bound on the number of events they may produce; compilation erases the bound. This chain satisfies RSC, by back-translating a
target context and finite prefix $m$ to a source context with bound $\mathrm{length}(m)$, but not RTP, since no source context produces an infinite trace.

## Depends on

- [Robust trace property preservation](robust-trace-property-preservation.md)
- [Robust safety property preservation](robust-safety-property-preservation.md)

## Proof depends on

- [Robust safety property preservation has a property-free characterization](rsp-has-a-property-free-characterization.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.2, Theorem 2.1 and its proof sketch.
