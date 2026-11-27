# Realizable multiclass PAC learning from finite Natarajan dimension with explicit sample size

Let $X$ be countable with measurable singletons, $\beta$ a finite label set with $k \ge 2$ elements, and $C$ a class of functions $X \to \beta$ that N-shatters no finite set of more than $d$ points. On any $m$ points, $C$ realizes at most $\sum_{i \le d}\binom{m}{i}\binom{k}{2}^i$ labelings (Ben-David, Cesa-Bianchi, Haussler and Long, Theorem 9, with labels $\{0, \dots, n\}$ and $k = n + 1$); since the misclassification pattern of a hypothesis on labelled points is determined by its labeling of their instances, this also bounds the growth function of the Boolean loss class $\{(x,y) \mapsto [c(x) \ne y] : c \in C\}$. If $C$ has Natarajan dimension $d$, there are absolute constants $C_1, C_2 > 0$ such that $C$ is PAC learnable over the distributions realizable by $C$ with sample complexity

$$
C_1 \frac{d + \log(1/\delta)}{\varepsilon} \le m_C(\varepsilon, \delta) \le C_2 \frac{d \log\big(\frac{kd}{\varepsilon}\big) + \log(1/\delta)}{\varepsilon}
$$

(Shalev-Shwartz and Ben-David, Theorem 29.3, item 3).

## Proof sketch

The upper bound follows the binary proof with Natarajan's lemma in place of Sauer's lemma (Shalev-Shwartz and Ben-David, Section 29.2.1).

Derived (not stated in the cited sources): applying the binary epsilon-net argument to the loss class at confidence $\delta/k^{2d}$, every consistent learner (in particular every empirical risk minimizer) is an $(\varepsilon, \delta)$-PAC learner over the distributions realizable by $C$ from $m \ge \frac{8}{\varepsilon}\big(d \ln\frac{48}{\varepsilon} + 2d \ln k + \ln\frac{4}{\delta}\big)$ examples, for $\varepsilon, \delta \in (0,1)$, so the realizable sample complexity is $O((d \ln(k/\varepsilon) + \ln(1/\delta))/\varepsilon)$.

## Depends on

- [Multiclass fundamental theorem (Natarajan bounds)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/multiclass-fundamental-theorem.md)
- [The realizable distribution family](../../occam-bound-for-consistent-learners/realizable-family.md)
- [A consistent learner for a finite class](../../occam-bound-for-consistent-learners/consistent-learner.md)
- [Natarajan's lemma](natarajans-lemma.md)

## Proof depends on

- [The epsilon-net theorem](../vc-sample-complexity-and-epsilon-nets/epsilon-net-theorem.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Theorem 29.3.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995; technical report version UCSC-CRL-93-31, University of California, Santa Cruz, 1993, Theorem 9: <https://tr.soe.ucsc.edu/sites/default/files/technical-reports/UCSC-CRL-93-31.pdf>.
