# Posterior probability of a class

Consider a naive Bayes model with a finite nonempty set of classes $C$, finitely many features $i \in \iota$ with finite value sets $V_i$, a prior on classes, and for each class and feature a distribution of the feature value. The posterior probability of class $c$ given a feature vector $x$ is the joint probability of $(c, x)$ divided by the evidence of $x$, the total joint probability of $x$ over all classes. When the evidence is $0$, the division by zero makes every posterior value $0$.
