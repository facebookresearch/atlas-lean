# Feature weight in the Bernoulli naive Bayes log-odds

For a naive Bayes model with two classes and Boolean features, the weight of feature $i$ in the log posterior odds of class `true` against class `false`, when all prior and conditional probabilities are strictly positive: $\log \frac{P(x_i = 1 \mid \text{true}) P(x_i = 0 \mid \text{false})}{P(x_i = 0 \mid \text{true}) P(x_i = 1 \mid \text{false})}$.
