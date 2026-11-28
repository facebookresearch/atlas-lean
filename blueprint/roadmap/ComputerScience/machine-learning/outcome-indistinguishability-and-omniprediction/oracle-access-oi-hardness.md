# Oracle- and code-access outcome indistinguishability is computationally hard

Fix $k \in \mathbb{N}$ and suppose that for some $\alpha > 0$ no randomized algorithm counts $k$-cliques in $n$-vertex graphs in time $o(n^{\alpha k})$. Then there are $X \subseteq \{0,1\}^{d^2}$ (inputs of $d^2$ bits, where $d$ plays the role of the number of graph vertices, so all time and query bounds below are in this $d$, not in the input length), an efficiently sampleable distribution $D^*$ and a class of distinguishers running in time $\tilde O(d^3)$ with $\tilde O(d)$ oracle queries such that, for $\varepsilon = 1/(100k)$, no predictor running in time $d^{\alpha k}\log^{-\omega(1)}(d)$ is $\varepsilon$-oracle-access outcome indistinguishable. By contrast, for distinguishers given by circuits of size $s$, sample-access (and no-access) OI predictors of circuit size $O(s/\varepsilon^2)$ always exist, and oracle-access OI predictors of size $s\cdot q^{O(1/\varepsilon^2)}$ exist for distinguishers making $q$ queries, so the clique bound shows this exponential dependence on $1/\varepsilon$ is necessary up to polynomial factors. Under the weaker assumption $\mathrm{BPP} \ne \mathrm{PSPACE}$, there are a distribution sampleable in time $\exp(\mathrm{poly}(d))$ and $\mathrm{poly}(d)$ polynomial-time distinguishers for which no polynomial-time predictor is $1/\mathrm{poly}(d)$-oracle-access OI. Since code access can simulate oracle access, the same lower bounds hold for code-access OI. Thus giving auditors query access to a predictor makes indistinguishability strictly harder to achieve than showing them only historical predictions.

## Proof sketch

The outcome distribution is built from a family of Boolean functions with scalable hardness: a function on large inputs can be computed by a fast reduction from its values on smaller inputs, while computing it is hard (here derived from counting $k$-cliques via a worst-case to average-case reduction). An oracle-access distinguisher checks, by querying the predictor on the inputs of this reduction, that the predictor's values are consistent with the function, which Nature's outcomes are; a predictor that passes all such checks can therefore be turned into a fast algorithm for the hard function, contradicting the assumption. Sample-access distinguishers see only $p(x)$ on the sampled point and cannot run the reduction.

## Depends on

- [Outcome indistinguishability and its access hierarchy](outcome-indistinguishability.md)

## Sources

- C. Dwork, M. P. Kim, O. Reingold, G. N. Rothblum, G. Yona, "Outcome Indistinguishability", STOC (2021), arXiv:2011.13426, Theorems 2–6 (Theorem 5 with domain $\{0,1\}^{d^2}$), Corollaries 6.9 and 6.11.
