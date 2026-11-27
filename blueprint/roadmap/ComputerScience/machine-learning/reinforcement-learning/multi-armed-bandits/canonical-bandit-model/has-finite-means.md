# Bandits with finite means

A stochastic bandit $\nu = (P_1, \dots, P_k)$ has finite means when every reward law has a finite first moment,
$\int |x| \, dP_i(x) < \infty$, so that the mean $\mu_i = \int x \, dP_i(x)$ of each arm is defined.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.4 ("we assume throughout that $\mu_a(\nu)$ exists and is finite for all actions"). <https://tor-lattimore.com/downloads/book/book.pdf>
