# Fixation probability with selection in the finite Wright–Fisher model

This node covers the probability that an allele is eventually fixed in a finite Wright–Fisher population
with selection. For a diploid population of $N$ adults in which zygotes formed by random union of gametes
undergo viability selection and $N$ survivors are then sampled, the number of copies of the allele is a
Markov chain on $\{0, \dots, 2N\}$ with explicit transition probabilities, and the fixation
probabilities $u_i$ solve the linear system $u_i = \sum_j P(j \mid i)\,u_j$ with $u_0 = 0$ and
$u_{2N} = 1$. Felsenstein notes that no algebraic expression for the solution in terms of $N$ and the
viabilities is known; the diffusion approximation replaces the system by the Kolmogorov backward equation, under the
assumption of large population size and small selection coefficients.

## Expansion

A sound expansion states the transition probabilities and the linear system for the chain, proves
existence and uniqueness of its solution with the boundary values, and then states, as separate pages,
properties of the exact fixation probabilities (for example their dependence on the initial number of
copies and on the selection coefficients) and a precise convergence statement relating them to the
diffusion approximation, each with its own source.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VII.8 "The Diffusion Approximation to Fixation Probabilities", subsections "The
  Wright–Fisher model with selection", "Exact fixation probabilities" and "The diffusion approximation",
  equations (VII-71)–(VII-79), pp. 320–323.
