# Achievability of the rate-distortion function

Let $S_1, S_2, \dots$ be independent and identically distributed with a nonnegative separable distortion measure
$d$, let $\varphi_S(D) = \inf\{I(S;\hat S) : \mathbb{E}\, d(S,\hat S) \le D\}$, and suppose
$D > D_0 = \inf\{D : \varphi_S(D) < \infty\}$ and $D_{\max} = \inf_{\hat s} \mathbb{E}\, d(S, \hat s) < \infty$. Then the
operational rate-distortion function satisfies $R(D) = \varphi_S(D)$; in particular every rate above $\varphi_S(D)$ is
achievable with expected distortion at most $D$ for all sufficiently large block lengths.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: AEP and typical sets (finite iid).

## Proof depends on

- [Converse for lossy source coding](converse-for-lossy-source-coding.md)
- [Covering lemma](covering-lemma.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft), Theorem 25.1. <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
