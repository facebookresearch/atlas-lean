# Soundness of the ID algorithm

Let $G$ be a semi-Markovian causal diagram (a DAG over observed variables with bidirected edges for
latent common causes) over finite-valued variables, and let $X$, $Y$ be disjoint sets of observed
variables. Whenever the Shpitser–Pearl ID algorithm, run on $(Y, X, G)$, returns an expression in the
observational distribution, that expression equals $P(y \mid \mathrm{do}(x))$ for every causal model
compatible with $G$ whose observational distribution is strictly positive. Each line of the
algorithm is justified by one of the rules of the do-calculus or by the c-component factorization of
Tian and Pearl.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: semi-Markovian causal models and their diagrams (bidirected edges for latent common causes), with the ID algorithm.
- Proof prerequisite: Tian-Pearl c-component factorization.

## Proof depends on

- [Rule 1 of the do-calculus](causal-bayesian-networks/do-calculus-rule1.md)
- [Rule 2 of the do-calculus](causal-bayesian-networks/do-calculus-rule2.md)
- [Rule 3 of the do-calculus](causal-bayesian-networks/do-calculus-rule3.md)

## Sources

- I. Shpitser and J. Pearl, *Identification of joint interventional distributions in recursive semi-Markovian causal models*, AAAI 2006 (author technical report R-327): algorithm ID (Figure 3) and the proof that it terminates and is sound. <http://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf>
- I. Shpitser and J. Pearl, *Identification of conditional interventional distributions*, UAI 2006 (technical report R-329): ID restated (Figure 2) with the soundness of the do-calculus and c-component factorization steps. <http://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf>
