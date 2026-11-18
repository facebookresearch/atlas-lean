# Two-class naive Bayes model

A two-class naive Bayes model over a set $J$ of features, feature $j$ taking values in a finite set $X_j$, consists of

- a prior $\pi$ with $0 < \pi < 1$ for the class "damaging";
- for each $j$, likelihoods $D_j(v) > 0$ and $B_j(v) > 0$ of the values $v \in X_j$ given "damaging" and given "benign", with $\sum_v D_j(v) = 1$ and $\sum_v B_j(v) = 1$.

The features are taken to be conditionally independent given the class.
