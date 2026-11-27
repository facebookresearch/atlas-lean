# Approximants and signatures for the modal μ-calculus

Let $\mathcal{M}$ be a Kripke model with finitely many states $n$, and $\mu X.\varphi$ a formula with $X$ occurring only positively in $\varphi$. Define the
approximants $\varphi^0 = \emptyset$ and $\varphi^{k+1} = [\![\varphi]\!]_{X \mapsto \varphi^k}$. Then

$$[\![\mu X.\varphi]\!] = \bigcup_{k \in \mathbb{N}} \varphi^k = \varphi^n.$$

Proof: by monotonicity the approximants form an increasing chain of subsets of an $n$-element set, so some $\varphi^k$ with $k \le n$ equals
$\varphi^{k+1}$ and is a fixed point; it is the least fixed point because every pre-fixed point contains each $\varphi^k$, by induction on $k$, and
$[\![\mu X.\varphi]\!]$ is the least pre-fixed point. Each state of $[\![\mu X.\varphi]\!]$ therefore has a least index $k$ with the state in $\varphi^k$.

## Depends on

- [Formulas of the modal μ-calculus](../modal-calculus/mu-formula.md)
- [Satisfaction in the modal μ-calculus](../modal-calculus/sat.md)

## Expansion

- Check the approximant statement against an opened source with a precise locator.
- Define the signature of a state for a formula as the tuple of least approximation indices for its $\mu$-variables, in the order of
  their binding, with the indexing relative to the enclosing fixpoints fixed, and state, from an opened source, that in the
  model-checking game Verifier has a strategy from every satisfied position along which signatures never increase lexicographically
  and strictly decrease whenever a $\mu$-variable is unfolded.

## Sources

- J. Bradfield and C. Stirling, "Modal mu-calculi", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Elsevier, 2007.
- C. Stirling, *Modal and Temporal Properties of Processes*, Springer, 2001.
