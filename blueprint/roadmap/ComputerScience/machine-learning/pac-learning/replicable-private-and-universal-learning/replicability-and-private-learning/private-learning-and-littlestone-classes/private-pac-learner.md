# Private PAC learners and their sample complexity

A learner $A : (X \times \{0,1\})^n \to \{0,1\}^X$ is **$(\varepsilon,\delta)$-differentially private** if $\Pr[A(S) \in E] \le e^{\varepsilon}\Pr[A(S') \in E] + \delta$ for all events $E$ and all samples $S, S'$ differing in one labelled example. It is an $(\alpha, \beta)$-accurate private PAC learner for $H$ if moreover, for every $H$-realizable distribution $D$, $\Pr_{S \sim D^n}[\mathrm{er}_D(A(S)) \le \alpha] \ge 1 - \beta$. The **private sample complexity** $\mathrm{SC}_{\varepsilon,\delta}(H,\alpha,\beta)$ is the least such $n$. The learner is **proper** if it always outputs a concept of $H$. A class is **privately learnable** if for all $\alpha, \beta \in (0,1)$ and some constant $\varepsilon$ (for instance $\varepsilon = 0.1$) and $\delta$ negligible in $n$ (for instance $\delta = O(1/(n^2 \log n))$) the private sample complexity is finite; the lower bounds below are stated already for constant accuracy $\alpha = \beta = 1/16$.

## Depends on

- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Neighbouring row databases](../../../../../cryptography/differential-privacy/hamming-adj.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- S. P. Kasiviswanathan, H. K. Lee, K. Nissim, S. Raskhodnikova, A. Smith, "What Can We Learn Privately?", FOCS (2008); SIAM Journal on Computing 40 (2011), arXiv:0803.0924, Definitions 3.1 and 3.2.
- A. Beimel, K. Nissim, U. Stemmer, "Characterizing the Sample Complexity of Private Learners", ITCS (2013), arXiv:1402.2224.
