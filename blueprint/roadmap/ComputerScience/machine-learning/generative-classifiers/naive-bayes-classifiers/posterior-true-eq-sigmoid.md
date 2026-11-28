# Naive Bayes is logistic in its posterior

With two classes, binary features and strictly
positive prior and conditional probabilities, the posterior probability of the class `true` is
the logistic function of an affine function of the features. Without positivity the posterior
can be exactly `0` or `1`, which no finite logistic score gives.
