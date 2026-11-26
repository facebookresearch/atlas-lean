# Bias of the Bernoulli naive Bayes log-odds

For a naive Bayes model with two classes and Boolean features, the bias of the log posterior odds of class `true` against class `false`, when all prior and conditional probabilities are strictly positive: $\log \frac{P(\text{true})}{P(\text{false})} + \sum_i \log \frac{P(x_i = 0 \mid \text{true})}{P(x_i = 0 \mid \text{false})}$.
