# Random walks on finite groups

Random walks on a finite group $G$ driven by a probability $Q$: the $k$-step law is the convolution power $Q^{*k}$ and the stationary law is uniform. Their rates of convergence in total variation are read off the Fourier transform of $Q$ at the irreducible representations of $G$ (the Diaconis–Shahshahani upper bound lemma), with lower bounds from test sets. Main examples: random walk on the circle $\mathbb{Z}/n$ and the cube $\mathbb{Z}_2^n$, random transpositions on $S_n$ (mixing at $\tfrac12 n\log n$) and riffle shuffles (Bayer–Diaconis).

- [Convolution powers on a finite abelian group](add-conv-pow.md)
- [Fourier transform of a convolution power on a finite abelian group](dft-fun-add-conv-pow.md)
- [Convolution theorem on a finite abelian group](dft-fun-fin-group-conv.md)
- [Upper bound lemma for a random walk on a finite abelian group](four-mul-tv-dist-add-conv-pow-sq-le.md)
- [Upper bound lemma on a finite abelian group](four-mul-tv-dist-uniform-sq-le.md)
- [Fourier transform of the random-transposition measure](fourier-random-transposition.md)
- [The random-transposition measure on the symmetric group](random-transposition.md)
- [The random-transposition measure is a class function](random-transposition-conj.md)
- [Number of rising sequences of an arrangement](rising-sequences.md)
- [Number of transpositions in the symmetric group](two-mul-card-is-swap.md)
- [The uniform distribution on a finite set](uniform.md)
- [Random transpositions: fewer than $\tfrac12 n \log n$ steps do not suffice (Diaconis–Shahshahani)](diaconis-shahshahani-lower.md)
- [Random transpositions: $\tfrac12 n \log n + cn$ steps suffice (Diaconis–Shahshahani)](diaconis-shahshahani-upper.md)
- [Bayer–Diaconis formula for $a$-shuffles](card-sort-eq.md)
- [Upper bound lemma (Diaconis–Shahshahani)](upper-bound-lemma.md)
- [Upper bound for random transpositions](four-mul-tv-dist-random-transposition-sq.md)
- [The random-transposition measure is a probability](sum-random-transposition.md)

## Related topics

- [Fourier transform on finite groups](../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/README.md):
  the representation-theoretic tools (convolution, Schur's lemma, Plancherel) behind the upper bound
  lemma.
- [Mixing times of Markov chains](../../markov-chains/mixing-times-of-markov-chains/README.md):
  a random walk on a finite group is a Markov chain with uniform stationary law; total variation,
  mixing and cutoff are defined there.
- [Fourier transform on finite abelian groups](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/README.md):
  the abelian transform used for walks on the circle and the cube.
- [Fisher–Yates shuffle](../../../ComputerScience/randomized-algorithms/fisher-yates-shuffle/README.md):
  exact generation of a uniform permutation, the benchmark for card-shuffling walks.
- [Dirichlet forms](../../markov-chains/dirichlet-forms/README.md): the Dirichlet form, spectral gap and log-Sobolev constant of a finite reversible chain.
