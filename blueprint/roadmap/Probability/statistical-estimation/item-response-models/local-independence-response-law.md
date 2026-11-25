# Law of locally independent binary responses

For a finite set $I$ of items and success probabilities $q_i \in [0, 1]$, $i \in I$, the law of locally independent binary responses is the probability mass function on response patterns $x : I \to \{0, 1\}$ given by

$$p(x) = \prod_{i \in I} \begin{cases} q_i & \text{if } x_i = 1, \\ 1 - q_i & \text{if } x_i = 0. \end{cases}$$

## Sources

- J. P. Weeks, "plink: An R package for linking mixed-format tests using IRT-based methods", *Journal of Statistical Software* 35(12), 2010, Section 2, Equation (1) (dichotomous models, here with scaling constant $D = 1$ and no lower asymptote)
- P. Mair and R. Hatzinger, "Extended Rasch modeling: the eRm package for the application of IRT models in R", *Journal of Statistical Software* 20(9), 2007, Section 3.1 (the Rasch model with local independence)
