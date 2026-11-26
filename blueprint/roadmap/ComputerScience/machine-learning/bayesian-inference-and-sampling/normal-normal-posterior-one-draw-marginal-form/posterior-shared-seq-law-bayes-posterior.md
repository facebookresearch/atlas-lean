# Dirichlet posterior of the shared law as a Bayes posterior

Let $\alpha_0, \dots, \alpha_n > 0$ and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$. Under the Dirichlet prior with parameters $\alpha$ and the categorical likelihood of $N$ independent draws, the posterior at the observed labels $s$ is the Dirichlet distribution with parameters $\alpha_i + c_i(s)$, where $c_i(s)$ is the number of occurrences of label $i$ in $s$.
