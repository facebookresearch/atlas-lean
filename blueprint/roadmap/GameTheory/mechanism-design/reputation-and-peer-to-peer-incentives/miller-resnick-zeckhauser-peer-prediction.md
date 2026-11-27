# Miller–Resnick–Zeckhauser peer prediction

Consider raters who receive conditionally i.i.d. private signals about a product type drawn from a common prior with full support, with signals stochastically relevant (distinct signals induce distinct posteriors over a peer's signal). Paying each rater the logarithmic score of its report's induced posterior prediction for a peer's report makes truthful reporting a strict Bayes–Nash equilibrium. The transfers can be scaled to cover any finite effort cost and balanced to sum to zero across raters by subtracting a third rater's score, preserving strict truthfulness. Uninformative constant reporting can also be an equilibrium.

## Proof sketch

Given a truthful peer, a rater's expected payment from reporting $s'$ is the expected log score of the posterior induced by $s'$ under its true posterior; strict propriety of the log score and stochastic relevance make the true signal the unique maximizer.

## Depends on

- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)
- [Characterization of proper scoring rules](../characterization-of-proper-scoring-rules.md)

## Proof depends on

- [Scoring rules and properness for finite outcomes](../remaining-clauses-of-scoring-rules-and-properness.md)

## Sources

- Nolan Miller, Paul Resnick and Richard Zeckhauser, "Eliciting Informative Feedback: The Peer-Prediction Method", Management Science, 2005.
- Eric Friedman, Paul Resnick and Rahul Sami, "Manipulation-Resistant Reputation Systems", Algorithmic Game Theory, Cambridge University Press, 2007.
