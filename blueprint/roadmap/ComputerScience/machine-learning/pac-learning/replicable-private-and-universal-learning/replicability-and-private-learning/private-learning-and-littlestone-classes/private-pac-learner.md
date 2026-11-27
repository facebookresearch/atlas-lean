# Private PAC learners and their sample complexity

A learner $A : (X \times \{0,1\})^n \to \{0,1\}^X$ is **$(\varepsilon,\delta)$-differentially private** if $\Pr[A(S) \in E] \le e^{\varepsilon}\Pr[A(S') \in E] + \delta$ for all events $E$ and all samples $S, S'$ differing in one labelled example. It is an $(\alpha, \beta)$-accurate private PAC learner for $H$ if moreover, for every $H$-realizable distribution $D$, $\Pr_{S \sim D^n,\, h \sim A(S)}[\mathrm{er}_D(h) \le \alpha] \ge 1 - \beta$, the probability being over both the sample and the learner's internal coins. The **private sample complexity** $\mathrm{SC}_{\varepsilon,\delta}(H,\alpha,\beta)$ is the least such $n$. The learner is **proper** if it always outputs a concept of $H$. A class is **privately learnable** if for all $\alpha, \beta \in (0,1)$ the private sample complexity is finite for some constant $\varepsilon$ and some $\delta$ that decreases with the sample size $n$. The private-learning lower bounds that use this definition (Alon, Livni, Malliaris and Moran's thresholds theorem and their Corollary 2) fix the concrete regime $\varepsilon = 0.1$ and $\delta = O(1/(n^2 \log n))$ at constant accuracy $\alpha = \beta = 1/16$; this $\delta$ is a specific inverse-polynomial rate, not negligible in the cryptographic sense of being $o(n^{-c})$ for every $c$, and the lower bounds are claimed only in this regime.

## Depends on

- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Neighbouring row databases](../../../../../cryptography/differential-privacy/hamming-adj.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- S. P. Kasiviswanathan, H. K. Lee, K. Nissim, S. Raskhodnikova, A. Smith, "What Can We Learn Privately?", FOCS (2008); SIAM Journal on Computing 40 (2011), arXiv:0803.0924, Definitions 3.1 and 3.2.
- A. Beimel, K. Nissim, U. Stemmer, "Characterizing the Sample Complexity of Private Learners", ITCS (2013), arXiv:1402.2224.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949, Section 3, Theorem 1 and Corollary 2.
