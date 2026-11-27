# Private PAC learners and their sample complexity

A learner $A : (X \times \{0,1\})^n \to \{0,1\}^X$ is **$(\varepsilon,\delta)$-differentially private** if $\Pr[A(S) \in E] \le e^{\varepsilon}\Pr[A(S') \in E] + \delta$ for all events $E$ and all samples $S, S'$ differing in one labelled example. It is an $(\alpha, \beta)$-accurate private PAC learner for $H$ if moreover, for every $H$-realizable distribution $D$, $\Pr_{S \sim D^n,\, h \sim A(S)}[\mathrm{er}_D(h) \le \alpha] \ge 1 - \beta$, the probability being over both the sample and the learner's internal coins. The **private sample complexity** $\mathrm{SC}_{\varepsilon,\delta}(H,\alpha,\beta)$ is the least such $n$. The learner is **proper** if it always outputs a concept of $H$.

A class $H$ is **privately learnable** (Alon, Livni, Malliaris and Moran, Section 3) if there are functions $\varepsilon(n) = o(1)$ and $\delta(n) = n^{-\omega(1)}$ of the sample size, the latter *negligible* (that is, $\delta(n) n^{c} \to 0$ for every constant $c$), and learners $A_n : (X \times \{0,1\})^n \to \{0,1\}^X$, $n \in \mathbb{N}$, such that each $A_n$ is $(\varepsilon(n), \delta(n))$-differentially private and, for all $\alpha, \beta \in (0,1)$, there is an $n_0$ with $A_n$ an $(\alpha, \beta)$-accurate private PAC learner for $H$ for every $n \ge n_0$. The privacy parameter is evaluated at the learner's own sample size; a $\delta$ that merely tends to zero does not suffice: running an $m$-sample non-private learner on a uniformly random $m$ of the $n$ examples is $(0, m/n)$-differentially private, so with $m = \lfloor \sqrt{n} \rfloor$ and $\delta(n) = n^{-1/2}$ even the thresholds over $\mathbb{N}$, of infinite Littlestone dimension, would qualify.

Separately, the explicit lower bounds of Alon, Livni, Malliaris and Moran (Theorem 1 and Corollary 2) are fixed-parameter statements: they concern a single learner with sample size $n$ that is $(1/16, 1/16)$-accurate and $(0.1, \delta)$-differentially private with $\delta = O(1/(n^2 \log n))$, a specific inverse-polynomial rate. A privately learnable class has such learners, since $\varepsilon(n) \le 0.1$ and $\delta(n) \le 1/(n^2 \log n)$ for all large $n$.

## Depends on

- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Neighbouring row databases](../../../../../cryptography/differential-privacy/hamming-adj.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- S. P. Kasiviswanathan, H. K. Lee, K. Nissim, S. Raskhodnikova, A. Smith, "What Can We Learn Privately?", FOCS (2008); SIAM Journal on Computing 40 (2011), arXiv:0803.0924, Definitions 3.1 and 3.2.
- A. Beimel, K. Nissim, U. Stemmer, "Characterizing the Sample Complexity of Private Learners", ITCS (2013), arXiv:1402.2224.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949, Section 3, Theorem 1 and Corollary 2.
