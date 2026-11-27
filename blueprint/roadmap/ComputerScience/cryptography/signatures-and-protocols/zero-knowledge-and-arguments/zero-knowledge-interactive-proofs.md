# Zero-knowledge interactive proofs

A pair of interactive machines $(P, V)$ is an *interactive proof system* for a language $L$ if $V$ is probabilistic polynomial time and:

- (*completeness*) for every $x \in L$ there is a witness string $y$ such that for every auxiliary string $z$, $V$ accepts in the interaction $P(x, y) \leftrightarrow V(x, z)$
  with probability $1$;
- (*soundness*) there is a negligible function $e$ such that for every $x \notin L$, every prover strategy $P^*$ and every auxiliary string $z$, $V$ rejects in
  $P^*(x) \leftrightarrow V(x, z)$ with probability greater than $1 - e(|x|)$.

It has *soundness error* $s$ if the soundness condition holds with $1 - e(|x|)$ replaced by $1 - s(|x|)$. For $L \in \mathsf{NP}$ with witness relation $R_L$, it has an
*efficient prover* if $P$ is probabilistic polynomial time and completeness holds for every $y \in R_L(x)$; soundness is still required against all provers.

An interactive proof with an efficient prover for $L \in \mathsf{NP}$ is *zero knowledge* if for every probabilistic polynomial-time verifier $V^*$ there is an expected
probabilistic polynomial-time simulator $S$ such that for every non-uniform probabilistic polynomial-time distinguisher $D$ there is a negligible function $e$
with which, for every $x \in L$, $y \in R_L(x)$ and $z$, $D$ distinguishes $\mathrm{view}_{V^*}[P(x, y) \leftrightarrow V^*(x, z)]$ from $S(x, z)$ with advantage at most $e(|x|)$, that is, $\bigl|\Pr[D(x, z, \mathrm{view}) = 1] - \Pr[D(x, z, S(x, z)) = 1]\bigr| \le e(|x|)$, so the two ensembles indexed by $(x, y, z)$ are computationally indistinguishable. It is
*perfect* zero knowledge if the two distributions are identical, and *honest-verifier* zero knowledge if the condition is required only for $V^* = V$, with a
probabilistic polynomial-time simulator. Zero knowledge is preserved under sequential repetition polynomially many times.

## Depends on

- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>: Definitions 116.1, 119.5, 121.1 and 121.2, the remarks on soundness error and perfect zero knowledge, and Theorem 175.1 (sequential composition).
