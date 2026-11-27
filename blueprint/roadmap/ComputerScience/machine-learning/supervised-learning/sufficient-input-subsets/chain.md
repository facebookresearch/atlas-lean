# Backward-selection chain of remaining feature sets

Let $\iota$ be a set of features, $g$ a real function on the finite subsets of $\iota$ (the
prediction when the features outside the subset are masked), and $\pi$ a rule choosing an element
$\pi(R) \in R$ of every nonempty finite set $R$. Backward selection from a finite set $R$ produces
the list of remaining sets $R_0 = R, R_1, \dots, R_{|R|} = \emptyset$, where
$R_{t+1} = R_t \setminus \{\pi(R_t)\}$ is $R_t$ with the feature chosen by $\pi$ masked.
