# Random selection rule

For a nonempty sample, of size $n \ge 1$, the random selection rule of the stochastic gradient method draws the indices $i_0, \dots, i_{T-1}$ independently and uniformly from $\{1, \dots, n\}$. Its law is the product of $T$ uniform distributions on $\{1, \dots, n\}$, a probability measure on the index sequences $\kappa : \{0, \dots, T-1\} \to \{1, \dots, n\}$. Under it, each step selects a given index with probability $1/n$. The size $n = 0$ is excluded: for $T \ge 1$ there is then no index sequence, and the product measure would have mass $0$.

The source also analyses the random permutation rule (one pass over a random permutation of the sample); it is not treated here.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Section 3 (random selection rule).
