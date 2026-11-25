# Scoring rules and properness for finite outcomes

For a finite outcome set $X$, a scoring rule assigns to a forecast $q \in \Delta(X)$ and an outcome $w$ a score $S(q, w) \in [-\infty, \infty)$; it is regular if
$S(q, w) > -\infty$ whenever $q(w) > 0$, and expected scores are taken with the convention $0 \cdot (-\infty) = 0$. A regular scoring rule is proper if
$\mathbb{E}_{w \sim p} S(p, w) \ge \mathbb{E}_{w \sim p} S(q, w)$ for all $p, q \in \Delta(X)$, and strictly proper if equality forces $q = p$. Strict propriety of
the logarithmic rule in its extended cross-entropy form follows from Gibbs' inequality and its equality case, listed under the proof
dependencies. This node collects these definitions and the interface between them and the cross-entropy statements.

## Expansion

A sound expansion has separate pages for:

1. **Scoring rules and properness:** the definitions above, with real-valued rules as the special case without $-\infty$ scores.
2. **Extended-real logarithmic rule:** $S(q, w) = \log q(w)$ with value $-\infty$ when $q(w) = 0$, and expected scores with the convention
   $0 \cdot (-\infty) = 0$.
3. **Transport:** strict propriety of this rule on the whole simplex, obtained from Gibbs' inequality and its equality case through the
   scoring-rule interface, since $\mathbb{E}_{w \sim p} \log q(w)$ is $-\ln 2$ times the cross-entropy in bits. A real-valued logarithmic rule that
   assigns a finite value to $q(w) = 0$, such as $0$, is not even proper on the closed simplex.

## Proof depends on

- [Gibbs' inequality](../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)
- [Equality in Gibbs' inequality](../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-iff.md)

## Sources

- CS269I Incentives in Computer Science Lecture #17: Scoring Rules and Peer Prediction — Tim Roughgarden, Stanford University (2016), Definitions 1.1–1.2 and Section 1.5. <https://timroughgarden.org/f16/l/l17.pdf>
- Strictly Proper Scoring Rules, Prediction, and Estimation — Gneiting and Raftery, JASA 102 (2007), Section 2 (scores in the extended real line; propriety) and Section 3.1, Definition 2 (regularity). <https://stat.uw.edu/raftery/Research/PDF/Gneiting2007jasa.pdf>
