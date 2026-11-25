# Talagrand's $\gamma_\alpha$ functional

For a real number $\alpha$ and a distance $d$ on $T$,

$$\gamma_\alpha(T, d) = \inf \sup_{t \in T} \sum_{n \ge 0} 2^{n/\alpha}\,\Delta(A_n(t)),$$

the infimum over all admissible sequences of partitions, where $\Delta$ is the diameter for $d$
(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, Definition 2.7.3).
The cases $\alpha = 2$ and $\alpha = 1$ matter most; $\gamma_2$ governs sub-Gaussian processes.
The source takes $\alpha > 0$; the formula makes sense for every real $\alpha$, with $2^{n/\alpha} = 1$ when
$\alpha = 0$ (as $n/0 = 0$), and the theorems below use $\alpha = 2$.

The value lies in $[0, \infty]$, so the definition makes sense for every admissible sequence,
including those along which the series diverges. The distance is any function
$d : T \times T \to [0, \infty]$, which covers both a metric and the canonical pseudo-distance of
a Gaussian process.

## Background

- [Admissible sequence of partitions](admissible-sequence.md): the sequences over which the
  infimum runs.
