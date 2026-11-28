# Mean of an arm

The mean of arm $i$ of a stochastic bandit $\nu = (P_1, \dots, P_k)$ is the Bochner integral
$\mu_i = \int x \, dP_i(x)$. It is the mean of $P_i$ when $P_i$ has a finite first moment, as for a bandit with
finite means, and $0$ otherwise, by the convention that the Bochner integral of a non-integrable function is $0$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.4. <https://tor-lattimore.com/downloads/book/book.pdf>
