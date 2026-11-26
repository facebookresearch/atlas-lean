# Preserving equivalences does not preserve robust safety

For a [compilation chain](compilation-chains-and-robust-satisfaction.md) consider the correctness criteria
$\mathrm{TP}$: $\forall W, t.\ W{\downarrow} \rightsquigarrow t \Rightarrow W \rightsquigarrow t$ for whole programs $W$ (backward simulation);
$\mathrm{SCC}$: $\forall \mathsf P, \mathsf C_S, t.\ \mathsf C_S{\downarrow}[\mathsf P{\downarrow}] \rightsquigarrow t \Rightarrow \mathsf C_S[\mathsf P] \rightsquigarrow t$ (separate compiler correctness, linking with
compiled source contexts); and $\mathrm{CCC}$: $\mathbf C_T \approx \mathsf C_S$ and $\mathbf C_T[\mathsf P{\downarrow}] \rightsquigarrow t$ imply $\mathsf C_S[\mathsf P] \rightsquigarrow t$, for a relation $\approx$
between target and source contexts.

**Theorem.** There is a compiler between two deterministic languages that satisfies [robust trace equivalence preservation](robust-trace-equivalence-preservation.md),
TP, SCC and CCC, but not [robust safety property preservation](robust-safety-property-preservation.md).

In the counterexample, source functions take booleans and the target has only numbers; the compiled function behaves as the source one on the encodings $0$ and
$1$ of the booleans but may behave insecurely on other inputs, which no source context can supply, so equivalences are preserved while a robust safety property
is not.

## Depends on

- [Robust trace equivalence preservation](robust-trace-equivalence-preservation.md)
- [Robust safety property preservation](robust-safety-property-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.1 (TP, SCC and CCC), Section 5, Theorem 5.2 and its proof, and Appendix E (Definition E.13 and a generalization of the counterexample).
