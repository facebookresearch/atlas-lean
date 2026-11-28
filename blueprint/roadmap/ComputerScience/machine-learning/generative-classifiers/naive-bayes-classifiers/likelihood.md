# Likelihood of labelled examples under naive Bayes

Consider a naive Bayes model with a finite nonempty set of classes $C$, finitely many features $i \in \iota$ with finite value sets $V_i$, a prior on classes, and for each class and feature a distribution of the feature value. Let $(y_k, x_k)_{k < m}$ be labelled data. The likelihood of the data, with labels $y_k \in C$ and feature vectors $x_k$, is the product over examples of the joint probability of $(y_k, x_k)$ under the naive Bayes model.
