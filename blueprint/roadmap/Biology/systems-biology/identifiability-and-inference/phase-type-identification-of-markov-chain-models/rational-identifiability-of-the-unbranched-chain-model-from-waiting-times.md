# Rational identifiability of the unbranched chain model from waiting times

**Setting.** A continuous-time Markov chain has $N$ unobservable states $1,\dots,N$ and one observable state $N+1$, which is entered only from state $N$ and left by a single return arc to a state $s\le N$. The waiting time between successive visits to $N+1$ (for example the time between transcription bursts) has a phase-type distribution whose survival function is multi-exponential,

$$\mathbb{P}(T>t) = \sum_{j=1}^{N} A_j\, e^{\lambda_j t}, \qquad \sum_j A_j = 1,$$

with $\lambda_j$ the eigenvalues of the generator restricted to the unobservable states (all negative for ergodic models). Conversely, every multi-exponential phase-type distribution with $N$ exponentials can be represented by such a chain with $N$ unobservable states. The *unbranched chain model* has forward rates $k_n^+$ ($n\to n+1$) and backward rates $k_n^-$ ($n+1\to n$) for $1\le n\le N-1$, and exit rate $k_N$ from state $N$ to $N+1$.

**Theorem.**

1. Call a model *solvable* if (i) its transition graph is strongly connected, (ii) it has exactly $2N-1$ transition rate parameters, and (iii) the equations relating the rates to $(A_j,\lambda_j)$ have unique solutions up to discrete symmetries on an open domain of dimension $2N-1$. A solvable model necessarily returns to $s=N$. (The hypothesis matters: the chain $1\to2\to3$ with rates $a,b$ and return $3\to1$, $N=2$, has $s=1$ and $(a,b)$ determined up to swapping, but only two rates, so it is not solvable in this sense.)
2. For the unbranched chain there is an algorithm producing rational functions $F_n^{\pm}$ with rational coefficients such that

$$k_n^{+} = F_n^{+}(A_1,\dots,A_{N-1},\lambda_1,\dots,\lambda_N), \qquad k_n^{-} = F_n^{-}(A_1,\dots,A_{N-1},\lambda_1,\dots,\lambda_N),$$

and $k_N=-\sum_jA_j\lambda_j$. So, on the open dense set where all rates are nonzero and the $\lambda_j$ are distinct, all transition rates are uniquely identifiable from the waiting-time distribution.
3. All solvable models generating the same phase-type distribution share the same lifetime of state $N$ and the same stationary probability of state $N$, so these quantities are model-independent.

## Expansion

Vieta's formulas relate the elementary symmetric functions of the $\lambda_j$ to the coefficients of the characteristic polynomial of the restricted generator, while the amplitudes $A_j$ are determined by eigenvector components at the return state. For a chain the eigenvector components satisfy a three-term recursion, and solving the resulting triangular system alternately for $k^{-}$ and $k^{+}$ from state $N$ downwards expresses every rate as a rational function of the observables.

## Sources

- O. Radulescu, D. Grigoriev, M. Seiss, M. Douaihy, "Identifying Markov chain models from time-to-event data: an algebraic approach", *Bulletin of Mathematical Biology* 87(1) (2024), 11, Sections 2–4, Definition 4, Propositions 2, 5 and 16, Theorem 11 and Remark 12, <https://doi.org/10.1007/s11538-024-01385-y> (preprint arXiv:2311.03593).
