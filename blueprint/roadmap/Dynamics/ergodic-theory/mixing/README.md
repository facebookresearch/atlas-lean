# Mixing

A measure-preserving transformation is mixing when every event, pulled back far enough along the dynamics, becomes
asymptotically independent of every other event: $\mu(A \cap T^{-n} B) \to \mu(A)\,\mu(B)$. Mixing is the
statistical property between ergodicity and the Kolmogorov and Bernoulli properties: a mixing map is ergodic, and so
are all its powers, while Bernoulli shifts, the dynamical form of sequences of independent trials, are the basic
mixing examples.

- [Strong mixing](is-mixing.md)
- [Mixing implies ergodicity](ergodic.md)
- [Powers of a mixing map are mixing](iterate.md)
- [Mixing maps are totally ergodic](ergodic-iterate.md)
- [The one-sided left shift](shift.md)
- [The shift reads the next symbol](shift-apply.md)
- [Iterates of the shift](shift-iterate-apply.md)
- [The two-sided left shift](two-sided-shift.md)
- [The shift is measurable](measurable-shift.md)
- [The shift preserves the product measure](measure-preserving-shift.md)
- [A cylinder event is independent of the far future](measure-cylinder-inter-preimage-iterate.md)
- [Bernoulli shifts are mixing](is-mixing-shift.md)
- [Bernoulli shifts are ergodic](ergodic-shift.md)

## Related topics

- [Genericity of weak mixing](../genericity-of-weak-mixing/README.md): weak mixing, the Cesàro-averaged
  form of mixing, lies between mixing and ergodicity, and Halmos showed it is generic.
- [Birkhoff ergodic theorem](../birkhoff-ergodic-theorem/README.md): ergodicity, which mixing implies, is
  the condition under which time averages equal space averages.
- [Kolmogorov–Sinai entropy](../kolmogorov-sinai-entropy/README.md): Bernoulli shifts, the basic mixing
  examples, are told apart by their entropy.
- [Translation invariance and ergodicity of the q = 2 random-cluster measures](../../../StatisticalMechanics/random-cluster-model/translation-invariance-and-ergodicity-of-the-q-2/README.md):
  the same argument, mixing on cylinder events implies ergodicity, for translation actions on
  configuration spaces.
- [Mixing times of Markov chains](../../../Probability/markov-chains/mixing-times-of-markov-chains/README.md):
  convergence of a Markov chain to its stationary law, the probabilistic counterpart of mixing for the
  shift of a stationary Markov chain.
