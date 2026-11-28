# Naive Bayes classifiers

- [Class count](class-count.md)
- [Parameters of a categorical naive Bayes model](params.md)
- [Joint probability of a class and features](joint.md)
- [Evidence of the features](evidence.md)
- [Posterior probability of a class](posterior.md)
- [Joint probabilities sum to one](sum-joint.md)
- [Posterior probabilities sum to one](sum-posterior.md)
- [The log joint is the log prior plus feature log probabilities](log-joint.md)

## The classifier

- [Naive Bayes classifier](classify.md)
- [The naive Bayes classifier maximizes the posterior](posterior-le-classify.md)
- [Accuracy of a naive Bayes classifier](accuracy.md)
- [Risk of a naive Bayes classifier](risk.md)
- [The naive Bayes classifier has maximal accuracy](accuracy-le-classify.md)
- [The naive Bayes classifier minimizes the 0-1 risk](risk-classify-le.md)

## Maximum likelihood estimation

- [Likelihood of labelled examples under naive Bayes](likelihood.md)
- [Feature-value count in a class](feat-count.md)
- [Maximum likelihood parameters of categorical naive Bayes](mle.md)
- [The naive Bayes likelihood factors into categorical likelihoods](likelihood-eq.md)
- [Count estimates maximize the categorical naive Bayes likelihood](likelihood-le-mle.md)

## Two classes and binary features: the posterior is logistic

- [Feature weight in the Bernoulli naive Bayes log-odds](bernoulli-weight.md)
- [Bias of the Bernoulli naive Bayes log-odds](bernoulli-bias.md)
- [Log posterior odds of Bernoulli naive Bayes are affine](log-joint-sub.md)
- [Naive Bayes is logistic in its posterior](posterior-true-eq-sigmoid.md)

## The multinomial model

- [Parameters of a multinomial naive Bayes model](mult-params.md)
- [Joint mass of a class and a document](joint-2.md)
- [The log joint is linear in the word counts](log-joint-2.md)
- [Likelihood of labelled documents](likelihood-2.md)
- [Word count in a class](word-count.md)
- [Maximum likelihood parameters of multinomial naive Bayes](mle-2.md)
- [Count estimates maximize the multinomial naive Bayes likelihood](likelihood-le-mle-2.md)
- [Laplace smoothing](is-max-on-word-laplace.md)
